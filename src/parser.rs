//! Implementation of the low-level statement parser for Metamath databases.
//!
//! The parser identifies the boundaries between statements, extracts their math
//! strings and proofs, does basic validity checking within statements, and
//! extracts a list of definitions which can be indexed by nameck.  This module
//! also defines the core datatypes used to represent source positions and
//! parsed statements, which are used by other analysis passes.
//!
//! Analysis passes are not a stable interface; use `Database` instead.
//!
//! The input of the parser is a byte string, which will typically consist of a
//! file except when the preparser is used; see the `database` module
//! documentation.  The output is one or more segments; the parser is
//! responsible for detecting includes and splitting statements appropriately,
//! although responsibility for following includes rests on the `segment_set`.

use diag::Diagnostic;
use std::cmp;
use std::cmp::Ordering;
use std::mem;
use std::slice;
use std::str;
use std::sync::Arc;

/// Shared reference to a buffer which will be parsed.
///
/// We use `u8` throughout the parser because Metamath databases are limited to
/// US-ASCII by the spec.  Since math symbols are used as tokens, if we wanted
/// to allow UTF-8 in the future it would be best to continue using `u8`,
/// although there would need to be a validity check (valid UTF-8 encodings are
/// always canonical) in `Scanner::get_raw` and the eighth-bit hack in
/// `scan_expression` would need to be reverted.
pub type BufferRef = Arc<Vec<u8>>;

/// Semantic type for positions in files.
///
/// Due to the use of half-open ranges, input files are limited to 4 GiB - 1.
pub type FilePos = u32;

/// Semantic type for statement indices.
///
/// Since the shortest possible statement is three bytes, this cannot overflow
/// before `FilePos` does.
///
/// smetamath3 uses SMM2 statement numbering semantics, and counts all
/// statements from the spec (including group open and group close), as well as
/// counting comments as their own statements.
pub type StatementIndex = i32;

/// Constant used in valid ranges to indicate the logical end of the database.
pub const NO_STATEMENT: StatementIndex = -1;

/// Semantic type for file-position ranges.
///
/// Spans will generally not be empty.  An empty span at position 0 is called a
/// null span used as a sentinel value by several functions.
#[derive(Copy,Clone,Eq,PartialEq,Debug,Default)]
pub struct Span {
    /// Index of first character of the range.
    pub start: FilePos,
    /// Index one past last character of the range.
    pub end: FilePos,
}

impl Span {
    /// Coercion from array index pairs.
    pub fn new(start: usize, end: usize) -> Span {
        Span {
            start: start as FilePos,
            end: end as FilePos,
        }
    }

    fn new2(start: FilePos, end: FilePos) -> Span {
        Span {
            start: start,
            end: end,
        }
    }

    /// Returns the null span.
    pub fn null() -> Span {
        Span::new(0, 0)
    }

    /// Checks for the null span, i.e. zero length at offset zero.
    pub fn is_null(self) -> bool {
        self.end == 0
    }

    /// Given a position span, extract the corresponding characters from a
    /// buffer.
    pub fn as_ref(self, buf: &[u8]) -> &[u8] {
        &buf[self.start as usize..self.end as usize]
    }
}

/// Semantic type for segment identifiers, as an opacified integer.
///
/// Since segment identifiers are reused between incremental runs, and new
/// segments can be inserted between any two existing segments, the internal
/// numeric order of segment identifiers need not mean anything at all and is
/// not exposed.  If you need to compare segment identifiers for order, get a
/// reference to the database's `SegmentOrder` object.
#[derive(Copy,Clone,Debug,Eq,PartialEq,Hash,Default)]
pub struct SegmentId(pub u32);

/// Semantic type for the index of a token in a statement.
///
/// Each token consumes at least two characters, plus a three-byte keyword and
/// space to introduce the math string at the beginning of the file, so this
/// cannot overflow for files of valid length.
pub type TokenIndex = i32;

/// Data structure which tracks the logical order of segment IDs, since they are
/// not intrinsically ordered.
///
/// This is an example of an "order-maintenance data structure", actually a very
/// simple one. We can plug in the Dietz & Sleator 1987 algorithm if this gets
/// too slow.
///
/// IDs are never reused after being released from the order, so they can be
/// used safely as part of change-tracking structures.
///
/// SegmentOrder implements the `Comparer` trait, allowing it to be used
/// polymorphically with the `cmp` method to order lists of segments,
/// statements, or tokens.
#[derive(Clone,Debug,Default)]
pub struct SegmentOrder {
    high_water: u32,
    order: Vec<SegmentId>,
    reverse: Vec<usize>,
}

impl SegmentOrder {
    /// Creates a new empty segment ordering.
    pub fn new() -> Self {
        // let mut n = SegmentOrder {
        //     high_water: 1,
        //     order: Vec::new(),
        //     reverse: Vec::new(),
        // };
        // n.alloc_id();
        // n.order.push(SegmentId(1));
        // n.reindex();
        // n
        SegmentOrder {
            high_water: 2,
            order: vec![SegmentId(1)],
            reverse: vec![0; 2],
        }
    }

    /// Each segment ordering has a single ID which will not be used otherwise;
    /// pass this to `new_before` to get an ID larger than all created IDs.
    pub fn start(&self) -> SegmentId {
        SegmentId(1)
    }

    fn alloc_id(&mut self) -> SegmentId {
        let index = self.high_water;
        assert!(index < u32::max_value());
        self.high_water += 1;
        SegmentId(index)
    }

    fn reindex(&mut self) {
        self.reverse = vec![0; self.high_water as usize];
        for (ordinal, &id) in self.order.iter().enumerate() {
            self.reverse[id.0 as usize] = ordinal;
        }
    }

    /// Indicates that an ID will no longer be used, allowing some memory to be
    /// freed.
    ///
    /// The ID itself will not be reissued.
    pub fn free_id(&mut self, id: SegmentId) {
        self.order.remove(self.reverse[id.0 as usize] as usize);
        self.reindex();
    }

    // pub fn new_after(&mut self, after: SegmentId) -> SegmentId {
    //     let id = self.alloc_id();
    //     self.order.insert(self.reverse[after.0 as usize] as usize + 1, id);
    //     self.reindex();
    //     id
    // }

    /// Gets a new ID, and adds it to the order before the named ID, or at the
    /// end if you pass `start()`.
    pub fn new_before(&mut self, after: SegmentId) -> SegmentId {
        let id = self.alloc_id();
        self.order.insert(self.reverse[after.0 as usize] as usize, id);
        self.reindex();
        id
    }
}

/// A trait for objects which can be used to order other datatypes.
pub trait Comparer<T> {
    /// Compares two objects, like `Ord::cmp`, but with additional state data
    /// from the comparer that can be used for the ordering.
    fn cmp(&self, left: &T, right: &T) -> Ordering;
}

impl Comparer<SegmentId> for SegmentOrder {
    fn cmp(&self, left: &SegmentId, right: &SegmentId) -> Ordering {
        self.reverse[left.0 as usize].cmp(&self.reverse[right.0 as usize])
    }
}

impl Comparer<StatementAddress> for SegmentOrder {
    fn cmp(&self, left: &StatementAddress, right: &StatementAddress) -> Ordering {
        let order = self.cmp(&left.segment_id, &right.segment_id);
        (order, left.index).cmp(&(Ordering::Equal, right.index))
    }
}

impl Comparer<TokenAddress> for SegmentOrder {
    fn cmp(&self, left: &TokenAddress, right: &TokenAddress) -> Ordering {
        let order = self.cmp(&left.statement, &right.statement);
        (order, left.token_index).cmp(&(Ordering::Equal, right.token_index))
    }
}

impl<'a, T, C: Comparer<T>> Comparer<T> for &'a C {
    fn cmp(&self, left: &T, right: &T) -> Ordering {
        (*self).cmp(left, right)
    }
}

/// A statement is located by giving its segment and index within the segment.
#[derive(Copy,Clone,Eq,PartialEq,Hash,Debug,Default)]
pub struct StatementAddress {
    /// Segment which contains the statement.
    pub segment_id: SegmentId,
    /// Zero-based index of the statement.
    pub index: StatementIndex,
}

impl StatementAddress {
    /// Constructs a statement address from its parts.
    pub fn new(segment_id: SegmentId, index: StatementIndex) -> Self {
        StatementAddress {
            segment_id: segment_id,
            index: index,
        }
    }
}

impl StatementAddress {
    /// Convert a statement address into a statement range from here to the
    /// logical end of the database.
    pub fn unbounded_range(self) -> GlobalRange {
        GlobalRange {
            start: self,
            end: NO_STATEMENT,
        }
    }
}

/// A token is located within a $c or $v by giving the address of the declaring
/// statement and the zero-based index within the math string.
///
/// In most cases you will use `Atom` instead, so the size of this struct, while
/// a bit silly, doesn't matter so much.
#[derive(Copy,Clone,Eq,PartialEq,Debug,Default)]
pub struct TokenAddress {
    /// Address of the statement in which the token is defined.
    pub statement: StatementAddress,
    /// Index of the token within the defining statement's math string.
    pub token_index: TokenIndex,
}

impl TokenAddress {
    /// Constructs a token address from parts.
    pub fn new3(segment_id: SegmentId, index: StatementIndex, token: TokenIndex) -> Self {
        TokenAddress {
            statement: StatementAddress::new(segment_id, index),
            token_index: token,
        }
    }
}

#[derive(Copy,Clone,Debug,Default)]
pub struct GlobalRange {
    pub start: StatementAddress,
    pub end: StatementIndex, // or NO_STATEMENT
}

pub type Token = Box<[u8]>;
pub type TokenPtr<'a> = &'a [u8];

pub fn copy_token(ptr: TokenPtr) -> Token {
    ptr.to_owned().into_boxed_slice()
}

// TODO this is rather meh.  I'd kind of like a consoldiated struct and I'd rather avoid the Strings
#[derive(Debug)]
pub struct GlobalDv {
    pub start: StatementIndex,
    pub vars: Vec<Token>,
}

#[derive(Eq,PartialEq,Copy,Clone,Debug)]
pub enum SymbolType {
    Variable,
    Constant,
}

#[derive(Debug)]
pub struct LabelDef {
    pub index: StatementIndex,
}

#[derive(Debug)]
pub struct SymbolDef {
    pub name: Token,
    pub stype: SymbolType,
    pub start: StatementIndex,
    pub ordinal: TokenIndex,
}

#[derive(Debug)]
pub struct FloatDef {
    pub start: StatementIndex,
    pub name: Token,
    pub label: Token,
    pub typecode: Token,
}

#[derive(Debug)]
pub struct LocalVarDef {
    pub index: StatementIndex,
    pub ordinal: TokenIndex,
}

/// This is a "dense" segment, which must be fully rebuilt in order to make any change.  We may in
/// the future have an "unpacked" segment which is used for active editing, as well as a "lazy" or
/// "mmap" segment type for fast incremental startup.
#[derive(Debug,Default)]
pub struct Segment {
    pub buffer: BufferRef,
    // straight outputs
    pub statements: Vec<Statement>,
    span_pool: Vec<Span>,
    pub diagnostics: Vec<(StatementIndex, Diagnostic)>,
    pub next_file: Span,
    // crossed outputs
    pub global_dvs: Vec<GlobalDv>,
    pub symbols: Vec<SymbolDef>,
    pub local_vars: Vec<LocalVarDef>,
    pub labels: Vec<LabelDef>,
    pub floats: Vec<FloatDef>,
}

impl<'a> SegmentRef<'a> {
    pub fn statement_iter(self) -> StatementIter<'a> {
        StatementIter {
            slice_iter: self.segment.statements.iter(),
            segment: self,
            index: 0,
        }
    }

    pub fn statement(self, index: StatementIndex) -> StatementRef<'a> {
        StatementRef {
            segment: self,
            statement: &self.segment.statements[index as usize],
            index: index,
        }
    }

    pub fn bytes(self) -> usize {
        self.segment.buffer.len()
    }
}

#[derive(Copy,Clone,Debug,Eq,PartialEq)]
pub enum StatementType {
    /// Psuedo statement used only to record end-of-file whitespace
    Eof,
    /// Statement is damaged enough that there's no sense passing it to later stages
    Invalid,
    Comment,
    TypesettingComment,
    FileInclude,
    Axiom,
    Provable,
    Essential,
    Floating,
    Disjoint,
    OpenGroup,
    CloseGroup,
    Constant,
    Variable,
}
use self::StatementType::*;

impl Default for StatementType {
    fn default() -> StatementType {
        Invalid
    }
}

impl StatementType {
    fn takes_label(self) -> bool {
        match self {
            Axiom | Provable | Essential | Floating => true,
            _ => false,
        }
    }

    fn takes_math(self) -> bool {
        match self {
            Axiom | Provable | Essential | Floating | Disjoint | Constant | Variable => true,
            _ => false,
        }
    }
}

#[derive(Copy,Clone,Debug)]
pub struct Statement {
    pub stype: StatementType,
    span: Span,
    label: Span,
    pub group: StatementIndex,
    pub group_end: StatementIndex,
    // indices into span_pool
    math_start: usize,
    proof_start: usize,
    proof_end: usize,
}

#[derive(Copy,Clone)]
pub struct SegmentRef<'a> {
    pub segment: &'a Arc<Segment>,
    pub id: SegmentId,
}

#[derive(Copy,Clone)]
pub struct StatementRef<'a> {
    pub segment: SegmentRef<'a>,
    pub statement: &'a Statement,
    pub index: StatementIndex,
}

impl<'a> StatementRef<'a> {
    pub fn address(&self) -> StatementAddress {
        StatementAddress {
            segment_id: self.segment.id,
            index: self.index,
        }
    }

    pub fn scope_range(&self) -> GlobalRange {
        GlobalRange {
            start: self.address(),
            end: self.statement.group_end,
        }
    }

    pub fn label(&self) -> &'a [u8] {
        self.statement.label.as_ref(&self.segment.segment.buffer)
    }

    pub fn math_iter(&self) -> TokenIter<'a> {
        let range = self.statement.math_start..self.statement.proof_start;
        TokenIter {
            slice_iter: self.segment.segment.span_pool[range].iter(),
            buffer: &self.segment.segment.buffer,
            stmt_address: self.address(),
            index: 0,
        }
    }

    pub fn span(&self) -> Span {
        self.statement.span
    }

    pub fn math_len(&self) -> TokenIndex {
        (self.statement.proof_start - self.statement.math_start) as TokenIndex
    }

    pub fn proof_len(&self) -> TokenIndex {
        (self.statement.proof_end - self.statement.proof_start) as TokenIndex
    }

    pub fn math_span(&self, ix: TokenIndex) -> Span {
        self.segment.segment.span_pool[self.statement.math_start + ix as usize]
    }

    pub fn proof_span(&self, ix: TokenIndex) -> Span {
        self.segment.segment.span_pool[self.statement.proof_start + ix as usize]
    }

    pub fn math_at(&self, ix: TokenIndex) -> TokenRef<'a> {
        TokenRef {
            slice: self.math_span(ix).as_ref(&self.segment.segment.buffer),
            address: TokenAddress {
                statement: self.address(),
                token_index: ix,
            },
        }
    }

    pub fn proof_slice_at(&self, ix: TokenIndex) -> TokenPtr<'a> {
        self.proof_span(ix).as_ref(&self.segment.segment.buffer)
    }
}

pub struct StatementIter<'a> {
    slice_iter: slice::Iter<'a, Statement>,
    segment: SegmentRef<'a>,
    index: StatementIndex,
}

impl<'a> Iterator for StatementIter<'a> {
    type Item = StatementRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.slice_iter.next().map(|st_ref| {
            let index = self.index;
            self.index += 1;
            StatementRef {
                segment: self.segment,
                statement: st_ref,
                index: index,
            }
        })
    }
}

pub struct TokenIter<'a> {
    slice_iter: slice::Iter<'a, Span>,
    buffer: &'a [u8],
    stmt_address: StatementAddress,
    index: TokenIndex,
}

#[derive(Copy,Clone)]
pub struct TokenRef<'a> {
    pub slice: &'a [u8],
    pub address: TokenAddress,
}

impl<'a> TokenRef<'a> {
    pub fn index(self) -> TokenIndex {
        self.address.token_index
    }
}

impl<'a> Iterator for TokenIter<'a> {
    type Item = TokenRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.slice_iter.next().map(|spanref| {
            let index = self.index;
            self.index += 1;
            TokenRef {
                slice: spanref.as_ref(self.buffer),
                address: TokenAddress {
                    statement: self.stmt_address,
                    token_index: index,
                },
            }
        })
    }
}

#[derive(Default)]
struct Scanner<'a> {
    buffer: &'a [u8],
    buffer_ref: BufferRef,
    position: FilePos,
    diagnostics: Vec<(StatementIndex, Diagnostic)>,
    span_pool: Vec<Span>,
    unget: Span,
    labels: Vec<Span>,
    statement_start: FilePos,
    statement_index: StatementIndex,
    statement_math_start: usize,
    statement_proof_start: usize,
    has_bad_labels: bool,
    invalidated: bool,
}

const MM_VALID_SPACES: u64 = (1u64 << 9) | (1u64 << 10) | (1u64 << 12) | (1u64 << 13) |
                             (1u64 << 32);

fn is_mm_space_c0(byte: u8) -> bool {
    (MM_VALID_SPACES & (1u64 << byte)) != 0
}

fn is_mm_space(byte: u8) -> bool {
    byte <= 32 && is_mm_space_c0(byte)
}

// TODO: add outline comment detection
#[derive(Eq,PartialEq,Copy,Clone)]
enum CommentType {
    Normal,
    Typesetting,
    Extra,
}

impl<'a> Scanner<'a> {
    fn diag(&mut self, diag: Diagnostic) {
        self.diagnostics.push((self.statement_index, diag));
    }

    fn get_raw(&mut self) -> Span {
        #[inline(never)]
        #[cold]
        fn badchar(slf: &mut Scanner, ix: usize) -> Span {
            let ch = slf.buffer[ix];
            let diag = Diagnostic::BadCharacter(ix, ch);
            slf.diagnostics.push((slf.statement_index, diag));
            return slf.get_raw();
        }

        let len = self.buffer.len();
        let mut ix = self.position as usize;

        while ix < len && self.buffer[ix] <= 32 {
            // For the purpose of error recovery, we consider C0 control characters to be
            // whitespace (following SMM2)
            if !is_mm_space_c0(self.buffer[ix]) {
                self.position = (ix + 1) as FilePos;
                return badchar(self, ix);
            }
            ix += 1;
        }

        let start = ix;
        while ix < len {
            if self.buffer[ix] <= 32 || self.buffer[ix] > 126 {
                if self.buffer[ix] <= 32 {
                    break;
                }
                // DEL or C1 control or non-ASCII bytes (presumably UTF-8)
                let badix = ix;
                // skip this "token"
                ix += 1;
                while ix < len && !is_mm_space(self.buffer[ix]) {
                    ix += 1;
                }
                self.position = ix as FilePos;
                return badchar(self, badix);
            }

            ix += 1;
        }

        self.position = ix as FilePos;
        if start == ix {
            Span::null()
        } else {
            Span::new(start, ix)
        }
    }

    fn get_comment(&mut self, opener: Span, mid_statement: bool) -> CommentType {
        let mut ctype = CommentType::Normal;
        let mut first = true;
        loop {
            let tok = self.get_raw();
            if tok.is_null() {
                break;
            }
            let tok_ref = tok.as_ref(self.buffer);
            if tok_ref == b"$)" {
                return ctype;
            } else if tok_ref == b"$j" || tok_ref == b"$t" {
                if !first {
                    self.diag(Diagnostic::CommentMarkerNotStart(tok))
                } else if mid_statement {
                    self.diag(Diagnostic::MidStatementCommentMarker(tok))
                } else {
                    ctype = if tok_ref == b"$j" {
                        CommentType::Extra
                    } else {
                        CommentType::Typesetting
                    }
                }
            } else if tok_ref.contains(&b'$') {
                let tok_str = str::from_utf8(tok_ref).unwrap();
                if tok_str.contains("$)") {
                    self.diag(Diagnostic::BadCommentEnd(tok, opener));
                }
                if tok_str.contains("$(") {
                    self.diag(Diagnostic::NestedComment(tok, opener));
                }
            }

            first = false;
        }

        let cspan = Span::new2(opener.start, self.buffer.len() as FilePos);
        self.diag(Diagnostic::UnclosedComment(cspan));
        ctype
    }

    fn get(&mut self) -> Span {
        if !self.unget.is_null() {
            return mem::replace(&mut self.unget, Span::null());
        }

        loop {
            let tok = self.get_raw();
            if tok.is_null() {
                return Span::null();
            }
            let tok_ref = tok.as_ref(self.buffer);
            if tok_ref == b"$(" {
                self.get_comment(tok, true);
            } else {
                return tok;
            }
        }
    }

    fn out_statement(&mut self, stype: StatementType, label: Span) -> Statement {
        Statement {
            stype: stype,
            label: label,
            math_start: self.statement_math_start,
            proof_start: self.statement_proof_start,
            proof_end: self.span_pool.len(),
            group: NO_STATEMENT,
            group_end: NO_STATEMENT,
            span: Span::new2(mem::replace(&mut self.statement_start, self.position),
                             self.position),
        }
    }

    fn get_comment_statement(&mut self) -> Option<Statement> {
        let ftok = if self.unget.is_null() {
            self.get_raw()
        } else {
            mem::replace(&mut self.unget, Span::null())
        };
        if ftok != Span::null() {
            let ftok_ref = ftok.as_ref(self.buffer);
            if ftok_ref == b"$(" {
                let ctype = self.get_comment(ftok, false);
                let stype = if ctype == CommentType::Typesetting {
                    TypesettingComment
                } else {
                    Comment
                };
                return Some(self.out_statement(stype, Span::null()));
            } else {
                self.unget = ftok;
            }
        }
        None
    }

    fn read_labels(&mut self) {
        self.has_bad_labels = false;
        self.labels.clear();
        loop {
            let ltok = self.get();
            if ltok.is_null() {
                break;
            }
            let lref = ltok.as_ref(self.buffer);
            if lref.contains(&b'$') {
                self.unget = ltok;
                break;
            } else if !is_valid_label(lref) {
                self.diag(Diagnostic::BadLabel(ltok));
                self.has_bad_labels = true;
            } else {
                self.labels.push(ltok);
            }
        }
    }

    fn get_no_label(&mut self) {
        // none of these are invalidations...
        for &lspan in &self.labels {
            self.diagnostics.push((self.statement_index, Diagnostic::SpuriousLabel(lspan)));
        }
    }

    fn get_label(&mut self) -> Span {
        match self.labels.len() {
            1 => self.labels[0],
            0 => {
                self.diag(Diagnostic::MissingLabel);
                self.invalidated = true;
                Span::null()
            }
            _ => {
                for &addl in self.labels.iter().skip(1) {
                    self.diagnostics
                        .push((self.statement_index,
                               Diagnostic::RepeatedLabel(addl, self.labels[0])));
                }
                // have to invalidate because we don't know which to use
                self.invalidated = true;
                Span::null()
            }
        }
    }

    fn get_string(&mut self, expect_proof: bool, is_proof: bool) -> bool {
        loop {
            let tokn = self.get();
            if tokn.is_null() {
                break;
            }
            let toknref = tokn.as_ref(self.buffer);
            if toknref.contains(&b'$') {
                if toknref == b"$." {
                    // string is closed with no proof
                    if expect_proof {
                        self.diag(Diagnostic::MissingProof(tokn));
                    }
                    return false;
                } else if toknref == b"$=" && !is_proof {
                    // string is closed with a proof
                    if !expect_proof {
                        self.diag(Diagnostic::SpuriousProof(tokn));
                    }
                    return true;
                } else {
                    // string is closed with no proof and with an error, whoops
                    self.unget = tokn;
                    break;
                }
            } else {
                self.span_pool.push(tokn);
            }
        }

        self.diag(if is_proof {
            Diagnostic::UnclosedProof
        } else {
            Diagnostic::UnclosedMath
        });
        return false;
    }

    fn get_strings(&mut self, want_proof: bool) {
        let has_proof = self.get_string(want_proof, false);
        self.statement_proof_start = self.span_pool.len();

        if self.statement_proof_start == self.statement_math_start {
            self.invalidated = true;
            // this is invalid for all types of math string
            self.diag(Diagnostic::EmptyMathString);
        }

        if has_proof {
            // diagnostic already generated if unwanted, but we still need to eat the proof
            self.get_string(false, true);
        } else {
            // diagnostic already generated if unwanted.  this is NOT an invalidation as $p
            // statements don't need proofs (I mean you should have a ? but we know what you mean)
        }
    }

    fn eat_invalid(&mut self) {
        loop {
            let tok = self.get();
            if tok.is_null() {
                break;
            }
            let tref = tok.as_ref(self.buffer);
            if tref == b"$." {
                // we're probably synchronized
                break;
            } else if tref == b"$=" {
                // this is definitely not it
            } else if tref.contains(&b'$') {
                // might be the start of the next statement
                self.unget = tok;
                break;
            }
        }
    }

    fn get_file_include(&mut self) -> Span {
        let mut res = Span::null();
        let mut count = 0;
        loop {
            let tok = self.get();
            if tok.is_null() {
                break;
            }
            let tref = tok.as_ref(self.buffer);
            if tref == b"$]" {
                if count == 0 {
                    self.diag(Diagnostic::EmptyFilename);
                    self.invalidated = true;
                } else if count > 1 {
                    self.diag(Diagnostic::FilenameSpaces);
                    self.invalidated = true;
                } else if res.as_ref(self.buffer).contains(&b'$') {
                    self.diag(Diagnostic::FilenameDollar);
                }
                return res;
            } else if tref.len() > 0 && tref[0] == b'$' {
                break;
            } else {
                count += 1;
                res = tok;
            }
        }
        self.diag(Diagnostic::UnclosedInclude);
        self.invalidated = true;
        return res;
    }

    fn get_statement(&mut self) -> Statement {
        self.statement_start = self.position;
        self.statement_math_start = self.span_pool.len();
        self.statement_proof_start = self.span_pool.len();

        if let Some(stmt) = self.get_comment_statement() {
            return stmt;
        }

        self.read_labels();

        let mut stype = Eof;
        let kwtok = self.get();
        if !kwtok.is_null() {
            let kwtok_ref = kwtok.as_ref(self.buffer);
            stype = if kwtok_ref.len() == 2 && kwtok_ref[0] == b'$' {
                match kwtok_ref[1] {
                    b'[' => FileInclude,
                    b'a' => Axiom,
                    b'c' => Constant,
                    b'd' => Disjoint,
                    b'e' => Essential,
                    b'f' => Floating,
                    b'p' => Provable,
                    b'v' => Variable,
                    b'{' => OpenGroup,
                    b'}' => CloseGroup,
                    _ => Invalid,
                }
            } else {
                Invalid
            };
            if stype == Invalid {
                self.diag(Diagnostic::UnknownKeyword(kwtok));
            }
        }
        self.invalidated = false;

        let mut label = if stype.takes_label() {
            self.get_label()
        } else {
            self.get_no_label();
            Span::null()
        };

        if stype.takes_math() {
            self.get_strings(stype == Provable);
        }

        let math_len = self.statement_proof_start - self.statement_math_start;
        match stype {
            FileInclude => {
                label = self.get_file_include();
            }
            Disjoint => {
                // math.len = 1 was caught above
                if math_len == 1 {
                    self.diag(Diagnostic::DisjointSingle);
                    self.invalidated = true;
                }
            }
            Floating => {
                if math_len != 0 && math_len != 2 {
                    self.diag(Diagnostic::BadFloating);
                    self.invalidated = true;
                }
            }
            Invalid => {
                // eat tokens to the next keyword rather than treating them as labels
                self.eat_invalid();
            }
            _ => {}
        }

        if self.invalidated {
            stype = Invalid;
        }

        self.out_statement(stype, label)
    }

    fn get_segment(&mut self) -> (Segment, bool) {
        let mut seg = Segment { buffer: self.buffer_ref.clone(), ..Segment::default() };
        let mut top_group = NO_STATEMENT;
        let is_end;
        let end_diag;

        loop {
            let index = seg.statements.len() as StatementIndex;
            self.statement_index = index;
            let mut stmt = self.get_statement();
            stmt.group = top_group;
            seg.statements.push(stmt);

            // TODO record name usage
            match seg.statements[index as usize].stype {
                OpenGroup => {
                    top_group = index;
                }
                CloseGroup => {
                    if top_group == NO_STATEMENT {
                        self.diagnostics.push((index, Diagnostic::UnmatchedCloseGroup));
                    } else {
                        seg.statements[top_group as usize].group_end = index;
                        top_group = seg.statements[top_group as usize].group;
                    }
                }
                Constant => {
                    if top_group != NO_STATEMENT {
                        self.diagnostics.push((index, Diagnostic::ConstantNotTopLevel));
                    }
                }
                Essential => {
                    if top_group == NO_STATEMENT {
                        self.diagnostics.push((index, Diagnostic::EssentialAtTopLevel));
                    }
                }
                FileInclude => {
                    seg.next_file = seg.statements[index as usize].label;
                    end_diag = Diagnostic::UnclosedBeforeInclude(index);
                    is_end = false;
                    break;
                }
                Eof => {
                    end_diag = Diagnostic::UnclosedBeforeEof;
                    is_end = true;
                    break;
                }
                _ => {}
            }
        }

        while top_group != NO_STATEMENT {
            seg.statements[top_group as usize].group_end = seg.statements.len() as StatementIndex;
            self.diagnostics.push((top_group, end_diag.clone()));
            top_group = seg.statements[top_group as usize].group;
        }

        for index in 0..seg.statements.len() {
            if seg.statements[index].group != NO_STATEMENT &&
               seg.statements[index].stype != OpenGroup {
                seg.statements[index].group_end =
                    seg.statements[seg.statements[index].group as usize].group_end;
            }
        }

        seg.diagnostics = mem::replace(&mut self.diagnostics, Vec::new());
        seg.span_pool = mem::replace(&mut self.span_pool, Vec::new());
        seg.span_pool.shrink_to_fit();
        seg.statements.shrink_to_fit();
        collect_definitions(&mut seg);
        (seg, is_end)
    }
}

fn collect_definitions(seg: &mut Segment) {
    let buf: &[u8] = &seg.buffer;
    for (index, &ref stmt) in seg.statements.iter().enumerate() {
        let index = index as StatementIndex;
        if stmt.stype.takes_label() {
            seg.labels.push(LabelDef { index: index });
        }

        if stmt.group_end != NO_STATEMENT {
            if stmt.stype == Variable {
                let math = &seg.span_pool[stmt.math_start..stmt.proof_start];
                for sindex in 0..math.len() {
                    seg.local_vars.push(LocalVarDef {
                        index: index,
                        ordinal: sindex as TokenIndex,
                    });
                }
            }
            continue;
        }

        let math = &seg.span_pool[stmt.math_start..stmt.proof_start];

        match stmt.stype {
            Constant => {
                for (sindex, &span) in math.iter().enumerate() {
                    seg.symbols.push(SymbolDef {
                        stype: SymbolType::Constant,
                        start: index,
                        name: copy_token(span.as_ref(buf)),
                        ordinal: sindex as TokenIndex,
                    });
                }
            }
            Variable => {
                for (sindex, &span) in math.iter().enumerate() {
                    seg.symbols.push(SymbolDef {
                        stype: SymbolType::Variable,
                        start: index,
                        name: copy_token(span.as_ref(buf)),
                        ordinal: sindex as TokenIndex,
                    });
                }
            }
            Disjoint => {
                seg.global_dvs.push(GlobalDv {
                    start: index,
                    vars: math.iter().map(|sp| copy_token(sp.as_ref(buf))).collect(),
                });
            }
            Floating => {
                seg.floats.push(FloatDef {
                    start: index,
                    typecode: copy_token(math[0].as_ref(buf)),
                    label: copy_token(stmt.label.as_ref(buf)),
                    name: copy_token(math[1].as_ref(buf)),
                });
            }
            _ => {}
        }
    }
}

fn is_valid_label(label: &[u8]) -> bool {
    label.iter().all(|&c| {
        c == b'.' || c == b'-' || c == b'_' || (c >= b'a' && c <= b'z') ||
        (c >= b'0' && c <= b'9') || (c >= b'A' && c <= b'Z')
    })
}

/// Slightly set.mm specific hack to extract a section name from a byte buffer.
///
/// This is run before parsing so it can't take advantage of comment extraction;
/// instead we look for the first indented line, within a heuristic limit of 500
/// bytes.
pub fn guess_buffer_name(buffer: &[u8]) -> &str {
    let buffer = &buffer[0..cmp::min(500, buffer.len())];
    let mut index = 0;
    while index < buffer.len() {
        if buffer[index] == b' ' {
            break;
        }
        while index < buffer.len() && buffer[index] != b'\n' {
            index += 1;
        }
        if index < buffer.len() {
            index += 1;
        }
    }
    // index points at the beginning of an indented line, or EOF

    while index < buffer.len() && buffer[index] == b' ' {
        index += 1;
    }

    let mut eol = index;
    while eol < buffer.len() && buffer[eol] != b'\n' {
        eol += 1;
    }
    while eol > index && (buffer[eol - 1] == b'\r' || buffer[eol - 1] == b' ') {
        eol -= 1;
    }

    if eol == index {
        "<no section name found>"
    } else {
        str::from_utf8(&buffer[index..eol]).unwrap_or("<invalid UTF-8 in section name>")
    }
}

/// This function implements parsing stage 1, which breaks down the metalanguage grammar, finding
/// all identifier definitions and inclusion statements.
///
/// There is an argument to be made that we shouldn't tokenize or store the math strings and proofs
/// at this stage, since they're bulky and can easily be generated on demand.
///
/// The current Metamath spec defines comments and file inclusions at the token level.  It is
/// useful for our purposes to parse comments that are strictly between statements as if they were
/// statements (SMM2 did this too; may revisit) and we require file inclusions to be between
/// statements at the top nesting level (this has been approved by Norman Megill).
pub fn parse_segments(input: &BufferRef) -> Vec<Arc<Segment>> {
    let mut closed_spans = Vec::new();
    let mut scanner = Scanner {
        buffer_ref: input.clone(),
        buffer: input,
        ..Scanner::default()
    };
    assert!(input.len() < FilePos::max_value() as usize);

    loop {
        let (seg, last) = scanner.get_segment();
        // we can almost use seg.next_file == Span::null here, but for the error case
        closed_spans.push(Arc::new(seg));
        if last {
            return closed_spans;
        }
    }
}

/// Creates a new empty segment as a container for an I/O error.
///
/// Every error must be associated with a statement in our design, so associate
/// it with the EOF statement of a zero-length segment.
pub fn dummy_segment(diag: Diagnostic) -> Arc<Segment> {
    let mut seg = parse_segments(&Arc::new(Vec::new())).pop().unwrap();
    Arc::get_mut(&mut seg).unwrap().diagnostics.push((0, diag));
    seg
}
