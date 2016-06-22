use database::DbOptions;
use itoken::IToken;
use itoken::ITokenRef;
use std::borrow::Borrow;
use std::hash::Hash;
use std::sync::Arc;
use std::u32;
use parser::{Comparer, Segment, SegmentId, SegmentOrder, SegmentRef, StatementAddress, SymbolType,
             Token, TokenAddress, TokenPtr};
use segment_set::SegmentSet;
use util;
use util::HashMap;
use util::HashSet;
use util::new_set;
// An earlier version of this module was tasked with detecting duplicate symbol errors;
// current task is just lookup

#[derive(Copy,Clone,Debug,PartialEq,Eq,Default,Hash)]
pub struct Atom(u32);

type NameSlot<A, V> = Vec<(A, V)>;

fn slot_insert<A, C, V>(slot: &mut NameSlot<A, V>, comparer: &C, address: A, value: V)
    where C: Comparer<A>
{
    slot.push((address, value));
    slot.sort_by(|x, y| comparer.cmp(&x.0, &y.0));
}

fn slot_remove<A: Eq, V>(slot: &mut NameSlot<A, V>, address: A) {
    slot.retain(|x| x.0 != address);
}

fn autoviv<K, V: Default>(map: &mut HashMap<K, V>, key: K) -> &mut V
    where K: Hash + Eq
{
    map.entry(key).or_insert_with(Default::default)
}

fn deviv<K, Q: ?Sized, V, F>(map: &mut HashMap<K, V>, key: &Q, fun: F)
    where F: FnOnce(&mut V),
          K: Borrow<Q>,
          Q: Hash + Eq,
          K: Hash + Eq,
          V: Default + Eq
{
    let kill = match map.get_mut(key) {
        None => false,
        Some(rval) => {
            fun(rval);
            *rval == Default::default()
        }
    };
    if kill {
        map.remove(key);
    }
}

#[derive(Default, PartialEq, Eq, Debug, Clone)]
struct SymbolInfo {
    atom: Atom,
    generation: usize,
    all: NameSlot<TokenAddress, SymbolType>,
    constant: NameSlot<TokenAddress, ()>,
    float: NameSlot<StatementAddress, (Token, Token, Atom)>,
}

#[derive(Default, PartialEq, Eq, Debug, Clone)]
struct LabelInfo {
    atom: Atom,
    generation: usize,
    labels: NameSlot<StatementAddress, ()>,
}

#[derive(Default,Debug,Clone)]
struct AtomTable {
    table: HashMap<IToken, Atom>,
    reverse: Vec<IToken>,
}

fn intern(table: &mut AtomTable, tok: &IToken) -> Atom {
    let next = Atom(table.table.len() as u32 + 1);
    match table.table.get(tok) {
        None => {}
        Some(atom) => return *atom,
    };
    table.table.insert(tok.clone(), next);
    if table.reverse.len() == 0 {
        table.reverse.push(IToken::default());
    }
    table.reverse.push(tok.clone());
    next
}

#[derive(Default,Debug,Clone)]
pub struct Nameset {
    atom_table: AtomTable,
    options: Arc<DbOptions>,
    pub order: Arc<SegmentOrder>,

    generation: usize,
    dv_gen: usize,
    segments: HashMap<SegmentId, Arc<Segment>>,
    dv_info: NameSlot<StatementAddress, Vec<Atom>>,
    labels: HashMap<IToken, LabelInfo>,
    symbols: HashMap<IToken, SymbolInfo>,
}

impl Nameset {
    pub fn new() -> Nameset {
        Nameset::default()
    }

    pub fn update(&mut self, segs: &SegmentSet) {
        self.order = segs.order.clone();
        self.generation = self.generation.checked_add(1).unwrap();
        self.options = segs.options.clone();

        let mut keys_to_remove = Vec::new();
        for (&seg_id, &ref seg) in &self.segments {
            let stale = match segs.segments.get(&seg_id) {
                None => true,
                Some(&(ref seg_new, _)) => !util::ptr_eq::<Segment>(&seg_new, seg),
            };

            if stale {
                keys_to_remove.push(seg_id);
            }
        }

        for seg_id in keys_to_remove {
            self.remove_segment(seg_id);
        }

        for (&seg_id, &(ref seg, _)) in &segs.segments {
            self.add_segment(seg_id, seg.clone());
        }
    }

    pub fn add_segment(&mut self, id: SegmentId, seg: Arc<Segment>) {
        if self.segments.contains_key(&id) {
            return;
        }

        self.segments.insert(id, seg.clone());
        let sref = SegmentRef {
            segment: &seg,
            id: id,
        };

        for &ref symdef in &seg.symbols {
            let name = IToken::from_slice(&symdef.name);
            let slot = autoviv(&mut self.symbols, name.clone());
            slot.generation = self.generation;
            if slot.atom == Atom::default() {
                slot.atom = intern(&mut self.atom_table, &name);
            }
            let address = TokenAddress::new3(id, symdef.start, symdef.ordinal);
            slot_insert(&mut slot.all, &*self.order, address, symdef.stype);
            if symdef.stype == SymbolType::Constant {
                slot_insert(&mut slot.constant, &*self.order, address, ());
            }
        }

        for &ref lsymdef in &seg.local_vars {
            let namesl = sref.statement(lsymdef.index).math_at(lsymdef.ordinal).slice;
            let name = IToken::from_slice(namesl);
            intern(&mut self.atom_table, &name);
        }

        for &ref labdef in &seg.labels {
            let labelr = sref.statement(labdef.index).label();
            let label = IToken::from_slice(labelr);
            let slot = autoviv(&mut self.labels, label.clone());
            slot.generation = self.generation;
            if self.options.incremental && slot.atom == Atom::default() {
                slot.atom = intern(&mut self.atom_table, &label);
            }
            slot_insert(&mut slot.labels,
                        &*self.order,
                        StatementAddress::new(id, labdef.index),
                        ());
        }

        for &ref floatdef in &seg.floats {
            let name = IToken::from_slice(&floatdef.name);
            let slot = autoviv(&mut self.symbols, name.clone());
            slot.generation = self.generation;
            if slot.atom == Atom::default() {
                slot.atom = intern(&mut self.atom_table, &name);
            }
            let address = StatementAddress::new(id, floatdef.start);
            let tcatom = intern(&mut self.atom_table, &IToken::from_slice(&floatdef.typecode));
            slot_insert(&mut slot.float,
                        &*self.order,
                        address,
                        (floatdef.label.clone(), floatdef.typecode.clone(), tcatom));
        }

        for &ref dvdef in &seg.global_dvs {
            let vars = dvdef.vars.iter().map(|v| {
                intern(&mut self.atom_table, &IToken::from_slice(v))
            }).collect();
            self.dv_gen = self.generation;
            slot_insert(&mut self.dv_info,
                        &*self.order,
                        StatementAddress::new(id, dvdef.start),
                        vars);
        }
    }

    pub fn remove_segment(&mut self, id: SegmentId) {
        if let Some(seg) = self.segments.remove(&id) {
            let sref = SegmentRef {
                segment: &seg,
                id: id,
            };
            let gen = self.generation;
            for &ref symdef in &seg.symbols {
                let name = ITokenRef::from(&symdef.name);
                deviv(&mut self.symbols, name, |slot| {
                    let address = TokenAddress::new3(id, symdef.start, symdef.ordinal);
                    slot.generation = gen;
                    slot_remove(&mut slot.all, address);
                    slot_remove(&mut slot.constant, address);
                });
            }

            for &ref labdef in &seg.labels {
                let label = sref.statement(labdef.index).label();
                let labelt = ITokenRef::from(label);
                deviv(&mut self.labels, labelt, |slot| {
                    slot.generation = gen;
                    slot_remove(&mut slot.labels, StatementAddress::new(id, labdef.index));
                });
            }

            for &ref floatdef in &seg.floats {
                let name = ITokenRef::from(&floatdef.name);
                deviv(&mut self.symbols, name, |slot| {
                    let address = StatementAddress::new(id, floatdef.start);
                    slot.generation = gen;
                    slot_remove(&mut slot.float, address);
                });
            }

            for &ref dvdef in &seg.global_dvs {
                self.dv_gen = gen;
                slot_remove(&mut self.dv_info, StatementAddress::new(id, dvdef.start));
            }
        }
    }

    pub fn get_atom(&self, name: TokenPtr) -> Atom {
        let namet = ITokenRef::from(name);
        self.atom_table.table.get(namet).cloned().expect("please only use get_atom for local $v")
    }

    pub fn atom_name(&self, atom: Atom) -> TokenPtr {
        &self.atom_table.reverse[atom.0 as usize].as_slice()
    }

    pub fn atom_name_itok(&self, atom: Atom) -> &IToken {
        &self.atom_table.reverse[atom.0 as usize]
    }
}

pub struct NameReader<'a> {
    nameset: &'a Nameset,
    incremental: bool,
    found_symbol: HashSet<Atom>,
    not_found_symbol: HashSet<IToken>,
    found_label: HashSet<Atom>,
    not_found_label: HashSet<IToken>,
}

pub struct NameUsage {
    generation: usize,
    incremental: bool,
    found_symbol: HashSet<Atom>,
    not_found_symbol: HashSet<IToken>,
    found_label: HashSet<Atom>,
    not_found_label: HashSet<IToken>,
}

pub struct LookupLabel {
    /// Address of topmost statement with this label
    pub address: StatementAddress,
    /// Atom assigned to this label; only valid if incremental=true in options
    pub atom: Atom,
}

pub struct LookupSymbol {
    pub stype: SymbolType,
    pub atom: Atom,
    /// Address of topmost global $c/$v with this token
    pub address: TokenAddress,
    /// Address of topmost global $c, if any
    pub const_address: Option<TokenAddress>,
}

pub struct LookupFloat<'a> {
    // again, topmost global float
    pub address: StatementAddress,
    pub label: TokenPtr<'a>,
    pub typecode: TokenPtr<'a>,
    pub typecode_atom: Atom,
}

pub struct LookupGlobalDv<'a> {
    pub address: StatementAddress,
    pub vars: &'a [Atom],
}

impl<'a> NameReader<'a> {
    pub fn new(nameset: &'a Nameset) -> Self {
        NameReader {
            nameset: nameset,
            incremental: nameset.options.incremental,
            found_symbol: new_set(),
            not_found_symbol: new_set(),
            found_label: new_set(),
            not_found_label: new_set(),
        }
    }

    pub fn into_usage(self) -> NameUsage {
        NameUsage {
            generation: self.nameset.generation,
            incremental: self.incremental,
            found_symbol: self.found_symbol,
            not_found_symbol: self.not_found_symbol,
            found_label: self.found_label,
            not_found_label: self.not_found_label,
        }
    }

    // TODO: add versions which fetch less data, to reduce dep tracking overhead
    pub fn lookup_label(&mut self, label: TokenPtr) -> Option<LookupLabel> {
        let labelt = ITokenRef::from(label);
        match self.nameset.labels.get(labelt) {
            Some(&ref lslot) => {
                if self.incremental {
                    self.found_label.insert(lslot.atom);
                }
                lslot.labels.first().map(|&(addr, _)| {
                    LookupLabel {
                        atom: lslot.atom,
                        address: addr,
                    }
                })
            }
            None => {
                if self.incremental {
                    self.not_found_label.insert(labelt.to_owned());
                }
                None
            }
        }
    }

    pub fn lookup_symbol(&mut self, symbol: TokenPtr) -> Option<LookupSymbol> {
        let symbolt = ITokenRef::from(symbol);
        match self.nameset.symbols.get(symbolt) {
            Some(&ref syminfo) => {
                if self.incremental {
                    self.found_symbol.insert(syminfo.atom);
                }
                syminfo.all.first().map(|&(addr, stype)| {
                    LookupSymbol {
                        stype: stype,
                        atom: syminfo.atom,
                        address: addr,
                        const_address: syminfo.constant.first().map(|&(addr, _)| addr),
                    }
                })
            }
            None => {
                if self.incremental {
                    self.not_found_symbol.insert(symbolt.to_owned());
                }
                None
            }
        }
    }

    // TODO: consider merging this with lookup_symbol
    pub fn lookup_float(&mut self, symbol: TokenPtr) -> Option<LookupFloat<'a>> {
        let symbolt = ITokenRef::from(symbol);
        match self.nameset.symbols.get(symbolt) {
            Some(&ref syminfo) => {
                if self.incremental {
                    self.found_symbol.insert(syminfo.atom);
                }
                syminfo.float.first().map(|&(addr, (ref label, ref typecode, tcatom))| {
                    LookupFloat {
                        address: addr,
                        label: &label,
                        typecode: &typecode,
                        typecode_atom: tcatom,
                    }
                })
            }
            None => {
                if self.incremental {
                    self.not_found_symbol.insert(symbolt.to_owned());
                }
                None
            }
        }
    }

    pub fn lookup_global_dv(&mut self) -> Vec<LookupGlobalDv> {
        self.nameset
            .dv_info
            .iter()
            .map(|&(addr, ref vars)| {
                LookupGlobalDv {
                    address: addr,
                    vars: &vars,
                }
            })
            .collect()
    }
}

impl NameUsage {
    pub fn valid(&self, nameset: &Nameset) -> bool {
        if nameset.dv_gen > self.generation {
            // we don't track fine-grained global DV usage
            return false;
        }

        if !self.incremental && nameset.generation > self.generation {
            // not tracking fine-grained deps today
            return false;
        }

        for &atom in &self.found_symbol {
            match nameset.symbols.get(nameset.atom_name_itok(atom)) {
                None => return false,
                Some(infop) => {
                    if infop.generation > self.generation {
                        return false;
                    }
                }
            }
        }

        for &ref name in &self.not_found_symbol {
            if nameset.symbols.contains_key(name) {
                return false;
            }
        }

        for &atom in &self.found_label {
            match nameset.labels.get(nameset.atom_name_itok(atom)) {
                None => return false,
                Some(infop) => {
                    if infop.generation > self.generation {
                        return false;
                    }
                }
            }
        }

        for &ref name in &self.not_found_label {
            if nameset.labels.contains_key(name) {
                return false;
            }
        }

        return true;
    }
}
