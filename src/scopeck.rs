//! This module calculates 3 things which are related only by the fact that they can be done
//! at the same time:
//!
//! 1. For $c $v $f and labelled statements ($e $f $a $p): Check for duplication
//!
//! 2. For $e $d $f $a $p: Check that all used math symbols are active in scope
//!
//! 3. For $a $p: Compute the frame
//!
//! Rules of precedence for error detection and recovery:
//!
//! 1. Math symbols and labels are actually in separate namespaces.  We warn about collisions but
//! otherwise do nothing.  Variables have responsibility for the warning.
//!
//! 2. When two definitions have overlapping live ranges, the earlier one wins.
//!
//! 3. Constant/nested variable collisions are special because they don't involve scope overlaps.
//! The constant wins, the variable must notify.

use bit_set::Bitset;
use diag::Diagnostic;
use nameck::Atom;
use nameck::NameReader;
use nameck::Nameset;
use nameck::NameUsage;
use parser;
use parser::Comparer;
use parser::copy_token;
use parser::GlobalRange;
use parser::NO_STATEMENT;
use parser::Segment;
use parser::SegmentId;
use parser::SegmentOrder;
use parser::SegmentRef;
use parser::StatementAddress;
use parser::StatementIndex;
use parser::StatementRef;
use parser::StatementType;
use parser::SymbolType;
use parser::Token;
use parser::TokenAddress;
use parser::TokenPtr;
use parser::TokenRef;
use segment_set::SegmentSet;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::ops::Range;
use std::sync::Arc;
use util::fast_extend;
use util::HashMap;
use util::HashSet;
use util::new_map;
use util::new_set;
use util::ptr_eq;

#[derive(Clone,Copy)]
struct LocalVarInfo {
    start: TokenAddress,
    end: StatementIndex,
    atom: Atom,
}

#[derive(Copy,Clone,Debug,Default)]
struct LocalFloatInfo {
    valid: GlobalRange,
    typecode: Atom,
}

#[derive(Copy,Clone,Debug)]
enum CheckedToken<'a> {
    Const(TokenPtr<'a>, Atom),
    Var(TokenPtr<'a>, Atom, LocalFloatInfo),
}

#[derive(Clone,Debug)]
struct LocalDvInfo {
    valid: GlobalRange,
    vars: Vec<Atom>,
}

#[derive(Clone,Debug)]
struct LocalEssentialInfo<'a> {
    valid: GlobalRange,
    label: TokenPtr<'a>,
    string: Vec<CheckedToken<'a>>,
}

pub type VarIndex = usize;

#[derive(Clone,Debug)]
pub struct ExprFragment {
    pub prefix: Range<usize>,
    pub var: VarIndex,
}

#[derive(Clone,Debug)]
pub struct VerifyExpr {
    pub typecode: Atom,
    pub rump: Range<usize>,
    pub tail: Box<[ExprFragment]>,
}

impl Default for VerifyExpr {
    fn default() -> VerifyExpr {
        VerifyExpr {
            typecode: Atom::default(),
            rump: 0..0,
            tail: Box::default(),
        }
    }
}

#[derive(Clone,Debug)]
pub struct Hyp {
    pub address: StatementAddress,
    pub variable_index: VarIndex,
    pub expr: VerifyExpr,
}

impl Hyp {
    pub fn is_float(&self) -> bool {
        self.variable_index != !0
    }
}

#[derive(Clone,Debug,Default)]
pub struct Frame {
    pub stype: StatementType,
    pub valid: GlobalRange,
    pub label_atom: Atom,
    pub const_pool: Box<[u8]>,
    pub hypotheses: Box<[Hyp]>,
    pub target: VerifyExpr,
    pub stub_expr: Box<[u8]>,
    pub var_list: Box<[Atom]>,
    pub mandatory_count: usize,
    pub mandatory_dv: Box<[(VarIndex, VarIndex)]>,
    pub optional_dv: Box<[Bitset]>,
}

struct ScopeState<'a> {
    diagnostics: HashMap<StatementIndex, Vec<Diagnostic>>,
    // segment: &'a Segment,
    order: &'a SegmentOrder,
    nameset: &'a Nameset,
    gnames: NameReader<'a>,
    local_vars: HashMap<Token, Vec<LocalVarInfo>>,
    local_floats: HashMap<Token, Vec<LocalFloatInfo>>,
    local_dv: Vec<LocalDvInfo>,
    local_essen: Vec<LocalEssentialInfo<'a>>,
    frames_out: Vec<Frame>,
}

impl<'a> ScopeState<'a> {
    fn push_diagnostic(&mut self, ix: StatementIndex, diag: Diagnostic) {
        self.diagnostics.entry(ix).or_insert(Vec::new()).push(diag);
    }

    // atom will be meaningless in non-incremental mode
    fn check_label_dup(&mut self, sref: StatementRef) -> Option<Atom> {
        // is the label unique in the database?
        if let Some(def) = self.gnames.lookup_label(sref.label()) {
            if def.address != sref.address() {
                self.push_diagnostic(sref.index, Diagnostic::DuplicateLabel(def.address));
                return None;
            }
            return Some(def.atom);
        }
        unreachable!()
    }

    fn check_math_symbol(&mut self,
                         sref: StatementRef,
                         tref: TokenRef)
                         -> Option<(SymbolType, Atom)> {
        // active global definition?
        if let Some(sdef) = self.gnames.lookup_symbol(tref.slice) {
            if self.order.cmp(&sdef.address, &tref.address) == Ordering::Less {
                return Some((sdef.stype, sdef.atom));
            }
        }

        // active local definition?
        if let Some(local_slot) = self.local_vars.get(tref.slice).and_then(|slot| slot.last()) {
            if check_endpoint(sref.index, local_slot.end) {
                return Some((SymbolType::Variable, local_slot.atom));
            }
        }

        self.push_diagnostic(sref.index, Diagnostic::NotActiveSymbol(tref.index()));
        return None;
    }

    fn lookup_float(&mut self, sref: StatementRef, tref: TokenRef) -> Option<LocalFloatInfo> {
        // active global definition?
        if let Some(fdef) = self.gnames.lookup_float(tref.slice) {
            if self.order.cmp(&fdef.address, &sref.address()) == Ordering::Less {
                return Some(LocalFloatInfo {
                    valid: fdef.address.unbounded_range(),
                    typecode: fdef.typecode_atom,
                });
            }
        }

        // active local definition?
        if let Some(&local_slot) = self.local_floats.get(tref.slice).and_then(|slot| slot.last()) {
            if check_endpoint(sref.index, local_slot.valid.end) {
                return Some(local_slot);
            }
        }

        None
    }

    fn check_eap(&mut self,
                 sref: StatementRef<'a>)
                 -> Option<Vec<CheckedToken<'a>>> {
        // does the math string consist of active tokens, where the first is a constant
        // and all variables have typecodes in scope?
        let mut bad = false;
        let mut out = Vec::with_capacity(sref.math_len() as usize);

        for tref in sref.math_iter() {
            match self.check_math_symbol(sref, tref) {
                None => bad = true,
                Some((SymbolType::Constant, atom)) => {
                    out.push(CheckedToken::Const(tref.slice, atom));
                }
                Some((SymbolType::Variable, atom)) => {
                    if tref.index() == 0 {
                        self.push_diagnostic(sref.index, Diagnostic::ExprNotConstantPrefix(0));
                        bad = true;
                    } else {
                        match self.lookup_float(sref, tref) {
                            None => {
                                self.push_diagnostic(sref.index, Diagnostic::VariableMissingFloat(tref.index()));
                                bad = true;
                            }
                            Some(lfi) => out.push(CheckedToken::Var(tref.slice, atom, lfi)),
                        }
                    }
                }
            }
        }

        if bad {
            None
        } else {
            Some(out)
        }
    }

    fn construct_stub_frame(&mut self, sref: StatementRef, latom: Atom, expr: &[CheckedToken]) {
        // gets data for $e and $f statements; these are not frames but they
        // are referenced by proofs using a frame-like structure
        let mut iter = expr.iter();
        let typecode = match iter.next().expect("parser checks $eap token count") {
            &CheckedToken::Const(_, typecode) => typecode,
            _ => unreachable!(),
        };
        let mut mvars = Vec::new();
        let mut conststr = Vec::new();

        while let Some(ctok) = iter.next() {
            match *ctok {
                CheckedToken::Const(tref, _) => {
                    conststr.extend_from_slice(tref);
                    *conststr.last_mut().unwrap() |= 0x80;
                }
                CheckedToken::Var(tref, atom, _) => {
                    conststr.extend_from_slice(tref);
                    *conststr.last_mut().unwrap() |= 0x80;
                    mvars.push(atom);
                }
            }
        }

        self.frames_out.push(Frame {
            stype: sref.statement.stype,
            label_atom: latom,
            valid: sref.scope_range(),
            hypotheses: Box::default(),
            target: VerifyExpr {
                typecode: typecode,
                rump: 0..0,
                tail: Box::default(),
            },
            const_pool: Box::default(),
            stub_expr: conststr.into_boxed_slice(),
            mandatory_count: mvars.len(),
            var_list: mvars.into_boxed_slice(),
            mandatory_dv: Box::default(),
            optional_dv: Box::default(),
        });
    }
}

struct InchoateFrame {
    variables: HashMap<Atom, (VarIndex, LocalFloatInfo)>,
    var_list: Vec<Atom>,
    mandatory_count: usize,
    mandatory_dv: Vec<(VarIndex, VarIndex)>,
    optional_dv: Vec<Bitset>,
    const_pool: Vec<u8>,
}

impl InchoateFrame {
    fn scan_expression<'a>(&mut self, expr: &[CheckedToken<'a>]) -> VerifyExpr {
        let mut iter = expr.iter();
        let head = match iter.next().expect("parser checks $eap token count") {
            &CheckedToken::Const(_, head) => head,
            _ => unreachable!(),
        };
        let mut open_const = self.const_pool.len();
        let mut tail = Vec::with_capacity(expr.len());

        for &ctok in iter {
            match ctok {
                CheckedToken::Const(tref, _) => {
                    fast_extend(&mut self.const_pool, tref);
                    *self.const_pool.last_mut().unwrap() |= 0x80;
                }
                CheckedToken::Var(_, atom, lfi) => {
                    let index = self.variables.get(&atom).map(|&(x, _)| x).unwrap_or_else(|| {
                        let index = self.variables.len();
                        self.var_list.push(atom);
                        self.optional_dv.push(Bitset::new());
                        self.variables.insert(atom, (index, lfi));
                        index
                    });
                    tail.push(ExprFragment {
                        prefix: open_const..self.const_pool.len(),
                        var: index,
                    });
                    open_const = self.const_pool.len();
                }
            }
        }

        VerifyExpr {
            typecode: head.to_owned(),
            rump: open_const..self.const_pool.len(),
            tail: tail.into_boxed_slice(),
        }
    }

    fn scan_dv<'a>(&mut self, var_set: &[Atom]) {
        // any variable encountered for the first time in a dv is an optional
        // variable, but we already checked validity in scope_check_dv
        let mut var_ids = Vec::with_capacity(var_set.len());

        for &varatom in var_set {
            let index = match self.variables.get(&varatom).map(|&(x, _)| x) {
                Some(mvarindex) => mvarindex,
                None => {
                    let index = self.variables.len();
                    self.var_list.push(varatom);
                    self.optional_dv.push(Bitset::new());
                    self.variables.insert(varatom, (index, Default::default()));
                    index
                }
            };
            var_ids.push(index);
        }

        for (leftpos, &leftid) in var_ids.iter().enumerate() {
            for &rightid in &var_ids[leftpos + 1..] {
                if !self.optional_dv[leftid].has_bit(rightid) {
                    self.optional_dv[leftid].set_bit(rightid);
                    self.optional_dv[rightid].set_bit(leftid);
                    if leftid < self.mandatory_count && rightid < self.mandatory_count {
                        self.mandatory_dv.push((leftid, rightid));
                    }
                }
            }
        }
    }
}

impl<'a> ScopeState<'a> {
    fn construct_full_frame(&mut self,
                            sref: StatementRef,
                            label_atom: Atom,
                            expr: &[CheckedToken]) {
        self.local_essen.retain(|hyp| check_endpoint(sref.index, hyp.valid.end));
        self.local_dv.retain(|hyp| check_endpoint(sref.index, hyp.valid.end));
        // local_essen and local_dv now contain only things still in scope

        // collect mandatory variables
        let mut iframe = InchoateFrame {
            variables: new_map(),
            var_list: Vec::new(),
            optional_dv: Vec::new(),
            mandatory_dv: Vec::new(),
            mandatory_count: 0,
            const_pool: Vec::new(),
        };
        let mut hyps = Vec::new();

        for ess in &self.local_essen {
            let scanned = iframe.scan_expression(&ess.string);
            hyps.push(Hyp {
                address: ess.valid.start,
                variable_index: !0,
                expr: scanned,
            });
        }

        let scan_res = iframe.scan_expression(expr);

        // include any mandatory $f hyps
        for &(index, ref lfi) in iframe.variables.values() {
            hyps.push(Hyp {
                address: lfi.valid.start,
                variable_index: index,
                expr: VerifyExpr {
                    typecode: lfi.typecode,
                    rump: 0..0,
                    tail: Box::default(),
                },
            })
        }

        hyps.sort_by(|h1, h2| self.order.cmp(&h1.address, &h2.address));
        iframe.mandatory_count = iframe.var_list.len();

        for dv in self.gnames.lookup_global_dv() {
            iframe.scan_dv(&dv.vars)
        }

        for dv in &self.local_dv {
            iframe.scan_dv(&dv.vars);
        }

        self.frames_out.push(Frame {
            stype: sref.statement.stype,
            label_atom: label_atom,
            valid: sref.address().unbounded_range(),
            hypotheses: hyps.into_boxed_slice(),
            target: scan_res,
            stub_expr: Box::default(),
            const_pool: iframe.const_pool.into_boxed_slice(),
            var_list: iframe.var_list.into_boxed_slice(),
            mandatory_count: iframe.mandatory_count,
            mandatory_dv: iframe.mandatory_dv.into_boxed_slice(),
            optional_dv: iframe.optional_dv.into_boxed_slice(),
        });
    }

    fn scope_check_axiom(&mut self, sref: StatementRef<'a>) {
        if let Some(latom) = self.check_label_dup(sref) {
            if let Some(expr) = self.check_eap(sref) {
                self.construct_full_frame(sref, latom, &expr);
            }
        }
    }

    fn scope_check_constant(&mut self, sref: StatementRef) {
        if sref.statement.group != NO_STATEMENT {
            // assert!(sref.statement.diagnostics.len() > 0);
            return;
        }

        for tokref in sref.math_iter() {
            if let Some(ldef) = self.gnames.lookup_label(tokref.slice) {
                self.push_diagnostic(sref.index,
                                     Diagnostic::SymbolDuplicatesLabel(tokref.index(),
                                                                       ldef.address));
            }

            if let Some(cdef) = self.gnames.lookup_symbol(tokref.slice) {
                if cdef.address != tokref.address {
                    self.push_diagnostic(sref.index,
                                         Diagnostic::SymbolRedeclared(tokref.index(),
                                                                      cdef.address));
                }
            }
        }
    }

    fn scope_check_dv(&mut self, sref: StatementRef) {
        let mut used = new_map();
        let mut bad = false;
        let mut vars = Vec::new();

        for tref in sref.math_iter() {
            match self.check_math_symbol(sref, tref) {
                None => {
                    bad = true;
                }
                Some((SymbolType::Constant, _)) => {
                    self.push_diagnostic(sref.index, Diagnostic::DjNotVariable(tref.index()));
                    bad = true;
                }
                Some((SymbolType::Variable, varat)) => {
                    if let Some(&previx) = used.get(&varat) {
                        self.push_diagnostic(sref.index,
                                             Diagnostic::DjRepeatedVariable(tref.index(), previx));
                        bad = true;
                        continue;
                    }

                    used.insert(varat, tref.index());
                    vars.push(varat);
                }
            }
        }

        if bad {
            return;
        }

        if sref.statement.group == NO_STATEMENT {
            return;
        }

        self.local_dv.push(LocalDvInfo {
            valid: sref.scope_range(),
            vars: vars,
        });
    }

    fn scope_check_essential(&mut self, sref: StatementRef<'a>) {
        let latom = self.check_label_dup(sref);
        if latom.is_none() {
            return;
        }
        if let Some(expr) = self.check_eap(sref) {
            self.local_essen.push(LocalEssentialInfo {
                valid: sref.scope_range(),
                label: sref.label(),
                string: expr,
            });
        }
    }

    fn scope_check_float(&mut self, sref: StatementRef) {
        let mut bad = false;
        assert!(sref.math_len() == 2);
        let const_tok = sref.math_at(0);
        let var_tok = sref.math_at(1);

        let latom = match self.check_label_dup(sref) {
            None => return,
            Some(a) => a,
        };

        let mut const_at = Atom::default();
        match self.check_math_symbol(sref, const_tok) {
            None => bad = true,
            Some((SymbolType::Constant, atom)) => const_at = atom,
            Some((SymbolType::Variable, _)) => {
                self.push_diagnostic(sref.index, Diagnostic::FloatNotConstant(0));
                bad = true;
            }
        }

        let mut var_at = Atom::default();
        match self.check_math_symbol(sref, var_tok) {
            None => bad = true,
            Some((SymbolType::Variable, atom)) => var_at = atom,
            _ => {
                self.push_diagnostic(sref.index, Diagnostic::FloatNotVariable(1));
                bad = true;
            }
        }

        if bad {
            return;
        }

        if let Some(prev) = self.lookup_float(sref, sref.math_at(1)) {
            self.push_diagnostic(sref.index, Diagnostic::FloatRedeclared(prev.valid.start));
            return;
        }

        // record the $f
        if sref.statement.group_end != NO_STATEMENT {
            self.local_floats
                .entry(copy_token(var_tok.slice))
                .or_insert(Vec::new())
                .push(LocalFloatInfo {
                    typecode: const_at,
                    valid: sref.scope_range(),
                });
        }

        let expr = [CheckedToken::Const(const_tok.slice, const_at),
                    CheckedToken::Var(var_tok.slice, var_at, LocalFloatInfo::default())];
        self.construct_stub_frame(sref, latom, &expr);
    }
}

fn check_endpoint(cur: StatementIndex, end: StatementIndex) -> bool {
    end == NO_STATEMENT || cur < end
}

impl<'a> ScopeState<'a> {
    // factored out to make a useful borrow scope
    fn maybe_add_local_var(&mut self,
                           sref: StatementRef,
                           tokref: TokenRef)
                           -> Option<TokenAddress> {
        let lv_slot = self.local_vars.entry(copy_token(tokref.slice)).or_insert(Vec::new());

        if let Some(lv_most_recent) = lv_slot.last() {
            if check_endpoint(sref.index, lv_most_recent.end) {
                return Some(lv_most_recent.start);
            }
        }

        lv_slot.push(LocalVarInfo {
            start: tokref.address,
            end: sref.statement.group_end,
            atom: self.nameset.get_atom(tokref.slice),
        });
        None
    }

    fn scope_check_provable(&mut self, sref: StatementRef<'a>) {
        if let Some(latom) = self.check_label_dup(sref) {
            if let Some(expr) = self.check_eap(sref) {
                self.construct_full_frame(sref, latom, &expr);
            }
        }
    }

    fn scope_check_variable(&mut self, sref: StatementRef) {
        for tokref in sref.math_iter() {
            if let Some(ldef) = self.gnames.lookup_label(tokref.slice) {
                self.push_diagnostic(sref.index,
                                     Diagnostic::SymbolDuplicatesLabel(tokref.index(),
                                                                       ldef.address));
            }

            if sref.statement.group == NO_STATEMENT {
                // top level $v, may conflict with a prior $c
                if let Some(cdef) = self.gnames.lookup_symbol(tokref.slice) {
                    if cdef.address != tokref.address {
                        self.push_diagnostic(sref.index,
                                             Diagnostic::SymbolRedeclared(tokref.index(),
                                                                          cdef.address));
                    }
                }
            } else {
                // nested $v, may conflict with an outer scope $v, top level $v/$c, or a _later_ $c
                if let Some(cdef) = self.gnames.lookup_symbol(tokref.slice) {
                    if self.order.cmp(&cdef.address, &tokref.address) == Ordering::Less {
                        self.push_diagnostic(sref.index,
                                             Diagnostic::SymbolRedeclared(tokref.index(),
                                                                          cdef.address));
                        continue;
                    } else if cdef.stype == SymbolType::Constant {
                        self.push_diagnostic(sref.index,
                            Diagnostic::VariableRedeclaredAsConstant(tokref.index(), cdef.address));
                        continue;
                    }
                }

                if let Some(prev_addr) = self.maybe_add_local_var(sref, tokref) {
                    // local/local conflict
                    self.push_diagnostic(sref.index,
                                         Diagnostic::SymbolRedeclared(tokref.index(), prev_addr));
                }
            }
        }
    }
}

pub struct SegmentScopeResult {
    id: SegmentId,
    source: Arc<Segment>,
    name_usage: NameUsage,
    diagnostics: HashMap<StatementIndex, Vec<Diagnostic>>,
    frames_out: Vec<Frame>,
}

pub fn scope_check_single(sset: &SegmentSet,
                          names: &Nameset,
                          seg: SegmentRef)
                          -> SegmentScopeResult {
    let mut state = ScopeState {
        diagnostics: new_map(),
        order: &sset.order,
        nameset: names,
        gnames: NameReader::new(names),
        local_vars: new_map(),
        local_floats: new_map(),
        local_dv: Vec::new(),
        local_essen: Vec::new(),
        frames_out: Vec::new(),
    };

    for sref in seg.statement_iter() {
        match sref.statement.stype {
            StatementType::Axiom => state.scope_check_axiom(sref),
            StatementType::Constant => state.scope_check_constant(sref),
            StatementType::Disjoint => state.scope_check_dv(sref),
            StatementType::Essential => state.scope_check_essential(sref),
            StatementType::Floating => state.scope_check_float(sref),
            StatementType::Provable => state.scope_check_provable(sref),
            StatementType::Variable => state.scope_check_variable(sref),
            _ => {}
        }
    }

    state.frames_out.shrink_to_fit();

    SegmentScopeResult {
        id: seg.id,
        source: seg.segment.clone(),
        name_usage: state.gnames.into_usage(),
        diagnostics: state.diagnostics,
        frames_out: state.frames_out,
    }
}

#[derive(Default, Clone)]
pub struct ScopeResult {
    incremental: bool,
    generation: usize,
    segments: Vec<Option<Arc<SegmentScopeResult>>>,
    frame_index: HashMap<Token, (usize, usize, usize)>,
}

impl ScopeResult {
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for (sid, ssro) in self.segments.iter().enumerate() {
            if let &Some(ref ssr) = ssro {
                for (&six, diag) in &ssr.diagnostics {
                    for d in diag {
                        out.push((StatementAddress::new(SegmentId(sid as u32), six), d.clone()));
                    }
                }
            }
        }
        out
    }
}

pub fn scope_check(result: &mut ScopeResult, segments: &Arc<SegmentSet>, names: &Arc<Nameset>) {
    result.incremental |= result.frame_index.is_empty();
    result.incremental &= segments.options.incremental;
    result.generation += 1;
    let gen = result.generation;
    let mut ssrq = VecDeque::new();
    // process all segments in parallel to get new scope results or identify reusable ones
    {
        let mut prev = new_map();
        for (sid, &ref ssr) in result.segments.iter().enumerate() {
            prev.insert(SegmentId(sid as u32), ssr.clone());
        }
        for sref in segments.segments() {
            let segments2 = segments.clone();
            let names = names.clone();
            let id = sref.id;
            let osr = prev.get(&id).and_then(|x| x.clone());
            ssrq.push_back(segments.exec.exec(sref.bytes(), move || {
                let sref = segments2.segment(id);
                if let Some(old_res) = osr {
                    if old_res.name_usage.valid(&names) && ptr_eq(&old_res.source, sref.segment) {
                        return None;
                    }
                }
                if segments2.options.trace_recalc {
                    println!("scopeck({:?})",
                             parser::guess_buffer_name(&sref.segment.buffer));
                }
                Some(Arc::new(scope_check_single(&segments2, &names, sref)))
            }));
        }
    }

    let mut stale_ids = new_set();
    let mut to_add = Vec::new();

    for (sid, res) in result.segments.iter().enumerate() {
        if res.is_some() {
            stale_ids.insert(SegmentId(sid as u32));
        }
    }

    for sref in segments.segments() {
        match ssrq.pop_front().unwrap().wait() {
            Some(scoperes) => {
                to_add.push(scoperes);
            }
            None => {
                stale_ids.remove(&sref.id);
            }
        }
    }

    for stale_id in stale_ids {
        let oseg = result.segments[stale_id.0 as usize].take().unwrap();
        let sref = SegmentRef {
            segment: &oseg.source,
            id: stale_id,
        };
        for frame in &oseg.frames_out {
            let label = sref.statement(frame.valid.start.index).label();
            result.frame_index.remove(label).expect("check_label_dup should prevent this");
        }
    }

    for res_new in to_add {
        let seg_index = res_new.id.0 as usize;
        if seg_index >= result.segments.len() {
            result.segments.resize(seg_index + 1, None);
        }

        let sref = segments.segment(res_new.id);
        for (index, frame) in res_new.frames_out.iter().enumerate() {
            let label = copy_token(sref.statement(frame.valid.start.index).label());
            let old = result.frame_index.insert(label, (gen, seg_index, index));
            assert!(old.is_none(), "check_label_dup should prevent this");
        }

        result.segments[seg_index] = Some(res_new);
    }
}

pub struct ScopeReader<'a> {
    result: &'a ScopeResult,
    incremental: bool,
    found: HashSet<Atom>,
    not_found: HashSet<Token>,
}

impl<'a> ScopeReader<'a> {
    pub fn new(res: &ScopeResult) -> ScopeReader {
        ScopeReader {
            result: res,
            incremental: res.incremental,
            found: new_set(),
            not_found: new_set(),
        }
    }

    pub fn into_usage(self) -> ScopeUsage {
        ScopeUsage {
            generation: self.result.generation,
            incremental: self.incremental,
            found: self.found,
            not_found: self.not_found,
        }
    }

    pub fn get(&mut self, name: TokenPtr) -> Option<&'a Frame> {
        match self.result.frame_index.get(name) {
            None => {
                if self.incremental {
                    self.not_found.insert(copy_token(name));
                }
                None
            }
            Some(&(_gen, segid, frix)) => {
                let framep = &self.result.segments[segid].as_ref().unwrap().frames_out[frix];
                if self.incremental {
                    self.found.insert(framep.label_atom);
                }
                Some(framep)
            }
        }
    }
}

pub struct ScopeUsage {
    generation: usize,
    incremental: bool,
    found: HashSet<Atom>,
    not_found: HashSet<Token>,
}

impl ScopeUsage {
    pub fn valid(&self, name: &Nameset, res: &ScopeResult) -> bool {
        (self.incremental || res.generation <= self.generation) &&
        self.found.iter().all(|&atom| match res.frame_index.get(name.atom_name(atom)) {
            None => false,
            Some(&(gen, _segid, _frix)) => gen <= self.generation,
        }) && self.not_found.iter().all(|name| !res.frame_index.contains_key(name))
    }
}
