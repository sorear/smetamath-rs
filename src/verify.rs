use bit_set::Bitset;
use diag::Diagnostic;
use nameck::{Atom, Nameset};
use parser::{self, Comparer, copy_token, NO_STATEMENT, Segment, SegmentId, SegmentOrder,
             SegmentRef, StatementAddress, StatementRef, StatementType, TokenPtr};
use scopeck::{self, ExprFragment, Frame, ScopeReader, ScopeResult, ScopeUsage, VerifyExpr};
use segment_set::SegmentSet;
use std::cmp::Ordering;
use std::mem;
use std::ops::Range;
use std::result;
use std::sync::Arc;
use std::u32;
use std::usize;
use util::copy_portion;
use util::fast_clear;
use util::fast_extend;
use util::HashMap;
use util::new_map;
use util::ptr_eq;
use self::PreparedStep::{Hyp, Assert};

enum PreparedStep<'a> {
    Hyp(Bitset, Atom, Range<usize>),
    Assert(&'a Frame),
}

struct StackSlot {
    vars: Bitset,
    code: Atom,
    expr: Range<usize>,
}

struct VerifyState<'a> {
    this_seg: SegmentRef<'a>,
    order: &'a SegmentOrder,
    nameset: &'a Nameset,
    scoper: ScopeReader<'a>,
    cur_frame: &'a Frame,
    prepared: Vec<PreparedStep<'a>>,
    stack: Vec<StackSlot>,
    stack_buffer: Vec<u8>,
    temp_buffer: Vec<u8>,
    subst_info: Vec<(Range<usize>, Bitset)>,
    var2bit: HashMap<Atom, usize>,
    dv_map: &'a [Bitset],
}

type Result = result::Result<(), Diagnostic>;

fn map_var<'a>(state: &mut VerifyState<'a>, token: Atom) -> usize {
    let nbit = state.var2bit.len();
    *state.var2bit.entry(token).or_insert(nbit)
}

impl<'a> VerifyState<'a> {
    // the initial hypotheses are accessed directly to avoid having to look up their names
    fn prepare_hypothesis(&mut self, hyp: &'a scopeck::Hyp) {
        let mut vars = Bitset::new();
        let tos = self.stack_buffer.len();

        if hyp.is_float() {
            fast_extend(&mut self.stack_buffer,
                        self.nameset.atom_name(self.cur_frame.var_list[hyp.variable_index]));
            *self.stack_buffer.last_mut().unwrap() |= 0x80;
            vars.set_bit(hyp.variable_index); // and we have prior knowledge it's identity mapped
        } else {
            for part in &*hyp.expr.tail {
                fast_extend(&mut self.stack_buffer,
                            &self.cur_frame.const_pool[part.prefix.clone()]);
                fast_extend(&mut self.stack_buffer,
                            self.nameset.atom_name(self.cur_frame.var_list[part.var]));
                *self.stack_buffer.last_mut().unwrap() |= 0x80;
                vars.set_bit(part.var); // and we have prior knowledge it's identity mapped
            }
            fast_extend(&mut self.stack_buffer,
                        &self.cur_frame.const_pool[hyp.expr.rump.clone()]);
        }

        let ntos = self.stack_buffer.len();
        self.prepared.push(Hyp(vars, hyp.expr.typecode, tos..ntos));
    }

    /// Adds a named $e hypothesis to the prepared array.  These are not kept in the frame
    /// array due to infrequent use, so other measures are needed.
    fn prepare_named_hyp(&mut self, label: TokenPtr) -> Result {
        for hyp in &*self.cur_frame.hypotheses {
            if hyp.is_float() {
                continue;
            }
            assert!(hyp.address.segment_id == self.this_seg.id);
            if self.this_seg.statement(hyp.address.index).label() == label {
                self.prepare_hypothesis(hyp);
                return Ok(());
            }
        }
        return Err(Diagnostic::StepMissing(copy_token(label)));
    }

    fn prepare_step(&mut self, label: TokenPtr) -> Result {
        let frame = match self.scoper.get(label) {
            Some(fp) => fp,
            None => return self.prepare_named_hyp(label),
        };

        let valid = frame.valid;
        let pos = self.cur_frame.valid.start;
        if self.order.cmp(&pos, &valid.start) != Ordering::Greater {
            return Err(Diagnostic::StepUsedBeforeDefinition(copy_token(label)));
        }

        if valid.end != NO_STATEMENT &&
           (pos.segment_id != valid.start.segment_id || pos.index >= valid.end) {
            return Err(Diagnostic::StepUsedAfterScope(copy_token(label)));
        }

        if frame.stype == StatementType::Axiom || frame.stype == StatementType::Provable {
            self.prepared.push(Assert(frame));
        } else {
            let mut vars = Bitset::new();

            for &var in &*frame.var_list {
                vars.set_bit(map_var(self, var));
            }

            let tos = self.stack_buffer.len();
            fast_extend(&mut self.stack_buffer, &frame.stub_expr);
            let ntos = self.stack_buffer.len();
            self.prepared
                .push(Hyp(vars, frame.target.typecode, tos..ntos));
        }

        return Ok(());
    }

    fn execute_step(&mut self, index: usize) -> Result {
        if index >= self.prepared.len() {
            return Err(Diagnostic::StepOutOfRange);
        }

        let fref = match self.prepared[index] {
            Hyp(ref vars, code, ref expr) => {
                self.stack.push(StackSlot {
                    vars: vars.clone(),
                    code: code,
                    expr: expr.clone(),
                });
                return Ok(());
            }
            Assert(fref) => fref,
        };

        if self.stack.len() < fref.hypotheses.len() {
            return Err(Diagnostic::ProofUnderflow);
        }
        let sbase = self.stack.len() - fref.hypotheses.len();

        while self.subst_info.len() < fref.mandatory_count {
            // this is mildly unhygenic, since slots corresponding to $e hyps won't get cleared, but
            // scopeck shouldn't generate references to them
            self.subst_info.push((0..0, Bitset::new()));
        }

        // check $f, build substitution
        // check $e
        // metamath spec guarantees $f will always come before any $e they affect (!)
        for (ix, hyp) in fref.hypotheses.iter().enumerate() {
            let slot = &self.stack[sbase + ix];

            // schedule a memory ref and nice predicable branch before the ugly branch
            if slot.code != hyp.expr.typecode {
                return Err(if hyp.is_float() {
                    Diagnostic::StepFloatWrongType
                } else {
                    Diagnostic::StepEssenWrongType
                });
            }

            if hyp.is_float() {
                self.subst_info[hyp.variable_index] = (slot.expr.clone(), slot.vars.clone());
            } else if !do_substitute_eq(&self.stack_buffer[slot.expr.clone()],
                                 fref,
                                 &hyp.expr,
                                 &self.subst_info,
                                 &self.stack_buffer) {
                return Err(Diagnostic::StepEssenWrong);
            }
        }

        let tos = self.stack_buffer.len();
        do_substitute(&mut self.stack_buffer, fref, &fref.target, &self.subst_info);
        let ntos = self.stack_buffer.len();

        self.stack.truncate(sbase);
        self.stack.push(StackSlot {
            code: fref.target.typecode,
            vars: do_substitute_vars(&fref.target.tail, &self.subst_info),
            expr: tos..ntos,
        });

        // check $d
        for &(ix1, ix2) in &*fref.mandatory_dv {
            for var1 in &self.subst_info[ix1].1 {
                for var2 in &self.subst_info[ix2].1 {
                    if var1 >= self.dv_map.len() || !self.dv_map[var1].has_bit(var2) {
                        return Err(Diagnostic::ProofDvViolation);
                    }
                }
            }
        }

        return Ok(());
    }

    fn finalize_step(&mut self) -> Result {
        if self.stack.len() == 0 {
            return Err(Diagnostic::ProofNoSteps);
        }
        if self.stack.len() > 1 {
            return Err(Diagnostic::ProofExcessEnd);
        }
        let tos = self.stack.last().unwrap();

        if tos.code != self.cur_frame.target.typecode {
            return Err(Diagnostic::ProofWrongTypeEnd);
        }

        fast_clear(&mut self.temp_buffer);
        do_substitute_raw(&mut self.temp_buffer, &self.cur_frame, self.nameset);

        if self.stack_buffer[tos.expr.clone()] != self.temp_buffer[..] {
            return Err(Diagnostic::ProofWrongExprEnd);
        }

        Ok(())
    }

    fn save_step(&mut self) {
        let top = self.stack.last().expect("can_save should prevent getting here");
        self.prepared.push(Hyp(top.vars.clone(), top.code, top.expr.clone()));
    }

    // proofs are not self-synchronizing, so it's not likely to get >1 usable error
    fn verify_proof(&mut self, stmt: StatementRef<'a>) -> Result {
        // only intend to check $p selfments
        if stmt.statement.stype != StatementType::Provable {
            return Ok(());
        }

        // no valid frame -> no use checking
        // may wish to record a secondary error?
        let cur_frame = match self.scoper.get(stmt.label()) {
            None => return Ok(()),
            Some(x) => x,
        };

        self.cur_frame = cur_frame;
        self.stack.clear();
        fast_clear(&mut self.stack_buffer);
        self.prepared.clear();
        self.var2bit.clear();
        self.dv_map = &cur_frame.optional_dv;
        // temp_buffer and subst_info are cleared before use

        for (index, &tokr) in cur_frame.var_list.iter().enumerate() {
            self.var2bit.insert(tokr, index);
        }

        if stmt.proof_slice_at(0) == b"(" {
            let mut i = 1;

            for hyp in &*cur_frame.hypotheses {
                self.prepare_hypothesis(hyp);
            }

            loop {
                if i >= stmt.proof_len() {
                    return Err(Diagnostic::ProofUnterminatedRoster);
                }
                let chunk = stmt.proof_slice_at(i);
                i += 1;

                if chunk == b")" {
                    break;
                }

                try!(self.prepare_step(chunk));
            }

            let mut k = 0usize;
            let mut can_save = false;
            while i < stmt.proof_len() {
                let chunk = stmt.proof_slice_at(i);
                for &ch in chunk {
                    if ch >= b'A' && ch <= b'T' {
                        k = k * 20 + (ch - b'A') as usize;
                        try!(self.execute_step(k));
                        k = 0;
                        can_save = true;
                    } else if ch >= b'U' && ch <= b'Y' {
                        k = k * 5 + 1 + (ch - b'U') as usize;
                        if k >= (u32::max_value() as usize / 20) - 1 {
                            return Err(Diagnostic::ProofMalformedVarint);
                        }
                        can_save = false;
                    } else if ch == b'Z' {
                        if !can_save {
                            return Err(Diagnostic::ProofInvalidSave);
                        }
                        self.save_step();
                        can_save = false;
                    } else if ch == b'?' {
                        if k > 0 {
                            return Err(Diagnostic::ProofMalformedVarint);
                        }
                        return Err(Diagnostic::ProofIncomplete);
                    }
                }
                i += 1;
            }

            if k > 0 {
                return Err(Diagnostic::ProofMalformedVarint);
            }
        } else {
            let mut count = 0;
            for i in 0..stmt.proof_len() {
                let chunk = stmt.proof_slice_at(i);
                if chunk == b"?" {
                    return Err(Diagnostic::ProofIncomplete);
                } else {
                    try!(self.prepare_step(chunk));
                    try!(self.execute_step(count));
                    count += 1;
                }
            }
        }

        try!(self.finalize_step());

        return Ok(());
    }
}

fn do_substitute(target: &mut Vec<u8>,
                 frame: &Frame,
                 expr: &VerifyExpr,
                 vars: &[(Range<usize>, Bitset)]) {
    for part in &*expr.tail {
        fast_extend(target, &frame.const_pool[part.prefix.clone()]);
        copy_portion(target, vars[part.var].0.clone());
    }
    fast_extend(target, &frame.const_pool[expr.rump.clone()]);
}

fn do_substitute_eq(mut compare: &[u8],
                    frame: &Frame,
                    expr: &VerifyExpr,
                    vars: &[(Range<usize>, Bitset)],
                    var_buffer: &[u8])
                    -> bool {
    fn step(compare: &mut &[u8], slice: &[u8]) -> bool {
        let len = slice.len();
        if compare.len() < len || slice != &(*compare)[0..len] {
            return true;
        }
        *compare = &(*compare)[len..];
        false
    }

    for part in &*expr.tail {
        if step(&mut compare, &frame.const_pool[part.prefix.clone()]) {
            return false;
        }
        if step(&mut compare, &var_buffer[vars[part.var].0.clone()]) {
            return false;
        }
    }

    !step(&mut compare, &frame.const_pool[expr.rump.clone()]) && compare.is_empty()
}

fn do_substitute_raw(target: &mut Vec<u8>, frame: &Frame, nameset: &Nameset) {
    for part in &*frame.target.tail {
        fast_extend(target, &frame.const_pool[part.prefix.clone()]);
        fast_extend(target, nameset.atom_name(frame.var_list[part.var]));
        *target.last_mut().unwrap() |= 0x80;
    }
    fast_extend(target, &frame.const_pool[frame.target.rump.clone()]);
}

fn do_substitute_vars(expr: &[ExprFragment], vars: &[(Range<usize>, Bitset)]) -> Bitset {
    let mut out = Bitset::new();
    for part in expr {
        out |= &vars[part.var].1;
    }
    out
}

struct VerifySegment {
    source: Arc<Segment>,
    scope_usage: ScopeUsage,
    diagnostics: HashMap<StatementAddress, Diagnostic>,
}

#[derive(Default,Clone)]
pub struct VerifyResult {
    segments: HashMap<SegmentId, Arc<VerifySegment>>,
}

impl VerifyResult {
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        self.segments
            .values()
            .flat_map(|vsr| vsr.diagnostics.iter().map(|(&sa, diag)| (sa, diag.clone())))
            .collect()
    }
}

fn verify_segment(sset: &SegmentSet,
                  nset: &Nameset,
                  scopes: &ScopeResult,
                  sid: SegmentId)
                  -> VerifySegment {
    let mut diagnostics = new_map();
    let dummy_frame = Frame::default();
    let sref = sset.segment(sid);
    let mut state = VerifyState {
        this_seg: sref,
        scoper: ScopeReader::new(scopes),
        nameset: nset,
        order: &sset.order,
        cur_frame: &dummy_frame,
        stack: Vec::new(),
        stack_buffer: Vec::new(),
        prepared: Vec::new(),
        temp_buffer: Vec::new(),
        subst_info: Vec::new(),
        var2bit: new_map(),
        dv_map: &dummy_frame.optional_dv,
    };
    for stmt in sref.statement_iter() {
        if let Err(diag) = state.verify_proof(stmt) {
            diagnostics.insert(stmt.address(), diag);
        }
    }
    VerifySegment {
        source: sref.segment.clone(),
        diagnostics: diagnostics,
        scope_usage: state.scoper.into_usage(),
    }
}

pub fn verify(result: &mut VerifyResult,
              segments: &Arc<SegmentSet>,
              nset: &Arc<Nameset>,
              scope: &Arc<ScopeResult>) {
    let old = mem::replace(&mut result.segments, new_map());
    let mut ssrq = Vec::new();
    for sref in segments.segments() {
        let segments2 = segments.clone();
        let nset = nset.clone();
        let scope = scope.clone();
        let id = sref.id;
        let old_res_o = old.get(&id).cloned();
        ssrq.push(segments.exec.exec(sref.bytes(), move || {
            let sref = segments2.segment(id);
            if let Some(old_res) = old_res_o {
                if old_res.scope_usage.valid(&nset, &scope) &&
                   ptr_eq::<Segment>(&old_res.source, sref.segment) {
                    return (id, old_res.clone());
                }
            }
            if segments2.options.trace_recalc {
                println!("verify({:?})",
                         parser::guess_buffer_name(&sref.segment.buffer));
            }
            (id, Arc::new(verify_segment(&segments2, &nset, &scope, id)))
        }))
    }

    result.segments.clear();
    for promise in ssrq {
        let (id, arc) = promise.wait();
        result.segments.insert(id, arc);
    }
}
