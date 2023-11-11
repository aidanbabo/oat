// todo: figure out references and stuff like what the hell ?!?

use std::collections::HashMap;
use std::fmt;

use super::ast;

type Mid = i64; // memory block id
type Fid = i64; // stack frame id
type Idx = i64; // index

#[derive(Clone, Debug, PartialEq)]
enum Bid {
    GlobalId(ast::Gid),
    HeapId(Mid),
    StackId(Fid),
    NullId,
}

impl fmt::Display for Bid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bid::GlobalId(gid) => write!(f, "@{gid}"),
            Bid::HeapId(mid) => write!(f, "M{mid}"),
            Bid::StackId(fid) => write!(f, "S{fid}"),
            Bid::NullId => write!(f, "null"),
        }
    }
}

#[derive(Clone, Debug)]
struct Ptr {
    ty: ast::Ty,
    bid: Bid,
    indices: Vec<Idx>, 
}

impl fmt::Display for Ptr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // todo: display for Ty
        write!(f, "{:?} {} ", self.ty, self.bid)?;
        let mut first = true;
        for idx in &self.indices {
            if first {
                write!(f, ", {idx}")?
               } else {
                write!(f, "{idx}")?
            }
            first = false;
        }
        Ok(())
    }
}

// stack value
#[derive(Clone, Debug)]
enum SVal {
    Undef,
    Int(i64),
    Ptr(Ptr),
}

impl fmt::Display for SVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SVal::Undef => write!(f, "undef"),
            SVal::Int(x) => write!(f, "{x}"),
            SVal::Ptr(p) => write!(f, "{p}"),
        }
    }
}

// memory tree and value
#[derive(Clone, Debug)]
enum MTree {
    Word(SVal),
    Str(String),
    Node(MVal),
}

impl fmt::Display for MTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MTree::Word(sv) => write!(f, "{sv}"),
            MTree::Str(s) => write!(f, "\"{s}\""),
            MTree::Node(m) => write!(f, "{m}"),
        }
    }
}

#[derive(Clone, Debug)]
struct MVal(Vec<MTree>);

impl fmt::Display for MVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        let mut first = true;
        for t in &self.0 {
            if first {
                write!(f, "{t}")?;
            } else {
                write!(f, " {t}")?;
            }
            first = false;
        }
        write!(f, "]")
    }
}

type Locals = HashMap<ast::Uid, SVal>;

#[derive(Clone)]
struct Config {
    globals: HashMap<ast::Gid, MVal>,
    heap: HashMap<Mid, MVal>,
    stack: HashMap<Fid, MVal>,
}

// this always adds a lists worth of indirection, why?
fn mval_of_gdecl(gd: ast::Gdecl) -> MVal {
    fn mtree_of_gdecl(gd: ast::Gdecl) -> MTree {
        match gd {
            (ty, ast::Ginit::Null) => MTree::Word(SVal::Ptr(Ptr {
                ty,
                bid: Bid::NullId,
                indices: vec![0],
            })),
            (ty, ast::Ginit::Gid(g)) => MTree::Word(SVal::Ptr(Ptr {
                ty,
                bid: Bid::GlobalId(g),
                indices: vec![0],
            })),
            (_, ast::Ginit::Bitcast(t1, v, _)) => mtree_of_gdecl((t1, *v)),
            (_, ast::Ginit::Int(i)) => MTree::Word(SVal::Int(i)),
            (_, ast::Ginit::String(s)) => MTree::Str(s),
            (_, ast::Ginit::Array(gs) | ast::Ginit::Struct(gs)) => MTree::Node(MVal(gs.into_iter().map(mtree_of_gdecl).collect())),
        }
    }
    MVal(vec![mtree_of_gdecl(gd)])
}

// undef constructor
fn mval_of_ty(named_types: &HashMap<ast::Tid, ast::Ty>, t: ast::Ty) -> MVal {
    fn mtree_of_ty(named_types: &HashMap<ast::Tid, ast::Ty>, t: ast::Ty) -> MTree {
        match t {
            ast::Ty::I1 | ast::Ty::I8 | ast::Ty::I64 | ast::Ty::Ptr(..) => MTree::Word(SVal::Undef),
            ast::Ty::Array(n, t) if *t == ast::Ty::I8 => MTree::Str(vec!['0'; n as usize].into_iter().collect()),
            ast::Ty::Array(n, _t) => MTree::Node(MVal(vec![MTree::Word(SVal::Undef); n as usize])),
            ast::Ty::Struct(ts) => MTree::Node(MVal(ts.into_iter().map(|t| mtree_of_ty(named_types, t)).collect())),
            ast::Ty::Fun(..) | ast::Ty::Void => unreachable!("shouldn't try to construct this type"),
            ast::Ty::Named(id) => mtree_of_ty(named_types, named_types[&id].clone()),
        }
    }
    MVal(vec![mtree_of_ty(named_types, t)])
}

enum ExecError {
    /// mem access not in bounds
    OOBIndexDeref,
    /// deref Null
    NullPtrDeref,
    /// deref Undef pointer (from bad GEP)
    UndefPtrDeref,
    /// deref pointer at wrong type (bad bitcast)
    IncompatTagDeref,
    /// read uninitialized memory
    UndefMemDeref,
    /// uninitialized memory load
    UninitMemLoad,
    /// deref freed stack/heap memory
    UseAfterFree,
}

fn interp_bop(b: ast::Bop, v1: SVal, v2: SVal) -> SVal {
    let (i, j) = match (v1, v2) {
        (SVal::Int(i), SVal::Int(j)) => (i, j),
        _ => panic!("invalid arg: interp_bop"),
    };
    let ret = match b {
        ast::Bop::Add => i.wrapping_add(j),
        ast::Bop::Sub => i.wrapping_sub(j),
        ast::Bop::Mul => i.wrapping_mul(j),
        // shift ops have weird behavior when wrapping
        // importantly these never panic and the ocaml ones
        // have UB where rust makes a weird choice
        ast::Bop::Shl => i.wrapping_shl(j.try_into().unwrap()),
        ast::Bop::Lshr => (i as u64).wrapping_shr((j as u64).try_into().unwrap()) as i64,
        ast::Bop::Ashr => i.wrapping_shr(j.try_into().unwrap()),
        ast::Bop::And => i & j,
        ast::Bop::Or => i | j,
        ast::Bop::Xor => i ^ j,
    };
    SVal::Int(ret)
}

fn interp_cnd(c: ast::Cnd, v1: SVal, v2: SVal) -> SVal {
    match (v1, v2, c) {
        (SVal::Ptr(p1), SVal::Ptr(p2), ast::Cnd::Eq) => {
            let b = p1.bid == p2.bid && p1.indices == p2.indices;
            SVal::Int(b as i64)
        }
        (SVal::Ptr(p1), SVal::Ptr(p2), ast::Cnd::Ne) => {
            let b = p1.bid != p2.bid || p1.indices != p2.indices;
            SVal::Int(b as i64)
        }
        (SVal::Int(i), SVal::Int(j), c) => {
            let b = match c {
                ast::Cnd::Eq => i == j,
                ast::Cnd::Ne => i != j,
                ast::Cnd::Slt => i < j,
                ast::Cnd::Sle => i <= j,
                ast::Cnd::Sgt => i > j,
                ast::Cnd::Sge => i >= j,
            };
            SVal::Int(b as i64)
        }
        _ => panic!("invalid arg: interp_cnd"),
    }
}

fn interp_i1(s: &SVal) -> bool {
    match s {
        SVal::Int(0) => false,
        SVal::Int(1) => false,
        _ => panic!("invalid arg: interp_i1"),
    }
}

fn interp_operand(named_types: &HashMap<ast::Tid, ast::Ty>, locals: &Locals, ty: &ast::Ty, o: &ast::Operand) -> SVal {
    match (ty, o) {
        (ast::Ty::I64, ast::Operand::Const(i)) |
        (ast::Ty::I1, ast::Operand::Const(i)) => SVal::Int(*i),
        (ast::Ty::Ptr(ty), ast::Operand::Null) => SVal::Ptr(Ptr {
            ty: (**ty).clone(),
            bid: Bid::NullId,
            indices: vec![0],
        }),
        (ast::Ty::Ptr(ty), ast::Operand::Gid(g)) => SVal::Ptr(Ptr {
            ty: (**ty).clone(),
            bid: Bid::GlobalId(g.clone()),
            indices: vec![0],
        }),
        (_, ast::Operand::Id(u)) => locals[u].clone(),
        (ast::Ty::Named(id), o) => interp_operand(named_types, locals, &named_types[&*id], o),
        _ => panic!("interp operand: malformed operand {o:?}:{ty:?}"),
    }
}

// this function is written OCaml style
fn load_idxs(m: &MVal, idxs: &[Idx]) -> Result<MTree, ExecError> {
    match idxs {
        [] => Ok(MTree::Node(m.clone())),
        [i, idxs@..] => {
            if *i < 0 || *i as usize > m.0.len() {
                return Err(ExecError::OOBIndexDeref);
            }

            match (idxs, &m.0[*i as usize]) {
                ([], mt) => Ok(mt.clone()),
                ([0], MTree::Str(s)) => Ok(MTree::Str(s.clone())),
                (_, MTree::Word(_)) => panic!("load idxs: attempted to index into word"),
                (_, MTree::Str(_)) => panic!("load idxs: attempted to index into word"),
                (_, MTree::Node(m)) => load_idxs(m, idxs),
            }
        }
    }
}

// this function is written OCaml style
fn store_idxs(m: &MVal, idxs: &[Idx], mt: &MTree) -> Result<MVal, ExecError> {
    match idxs {
        [] => Ok(MVal(vec![mt.clone()])),
        [i, idxs@..] => {
            if *i < 0 || *i > m.0.len() as i64 {
                return Err(ExecError::OOBIndexDeref);
            }
            let i = *i as usize;

            match (idxs, &m.0[i]) {
                ([], _) => {
                    let mut new_m = m.clone();
                    new_m.0[i] = mt.clone();
                    Ok(new_m)
                }
                (_, MTree::Word(_)) => panic!("load idxs: attempted to index into word"),
                (_, MTree::Str(_)) => panic!("load idxs: attempted to index into word"),
                (_, MTree::Node(new_m)) => {
                    let new_mt = MTree::Node(store_idxs(new_m, idxs, mt)?);
                    let mut new_m = m.clone();
                    new_m.0[i] = new_mt;
                    Ok(new_m)
                }
            }
        }
    }
}

fn load_bid(c: &Config, bid: &Bid) -> Result<MVal, ExecError> {
    match bid {
        Bid::NullId => return Err(ExecError::NullPtrDeref),
        Bid::HeapId(mid) => c.heap.get(mid).map(Clone::clone).ok_or(ExecError::UseAfterFree),
        Bid::GlobalId(gid) => Ok(c.globals.get(gid).expect("Load: bogus gid").clone()),
        Bid::StackId(fid) => c.stack.get(fid).map(Clone::clone).ok_or(ExecError::UseAfterFree),
    }
}

fn load_ptr(c: &Config, p: Ptr) -> Result<MTree, ExecError> {
    load_idxs(&load_bid(c, &p.bid)?, &p.indices)
}

fn store_ptr(c: &Config, p: &Ptr, mt: &MTree) -> Result<Config, ExecError> {
    let mval = load_bid(c, &p.bid)?;
    match &p.bid {
        Bid::NullId => return Err(ExecError::NullPtrDeref),
        Bid::HeapId(mid) => {
            let mval = store_idxs(&mval, &p.indices, mt)?;
            let mut config = c.clone();
            config.heap.insert(mid.clone(), mval);
            Ok(config)
        }
        Bid::GlobalId(gid) => {
            let mval = store_idxs(&mval, &p.indices, mt)?;
            let mut config = c.clone();
            config.globals.insert(gid.clone(), mval);
            Ok(config)
        }
        Bid::StackId(fid) => {
            let frame = store_idxs(&mval, &p.indices, mt)?;
            let mut config = c.clone();
            config.stack.insert(fid.clone(), frame);
            Ok(config)
        }
    }
}

// Tag and GEP implementation
fn effective_tag(named_types: &HashMap<ast::Tid, ast::Ty>, p: &Ptr) -> ast::Ty {
    let mut idxs = p.indices.get(1..).expect("effective_tag: invalid pointer to missing first index");
    let mut tag = &p.ty;
    while !idxs.is_empty() {
        match (tag, idxs) {
            (ast::Ty::Struct(ts), [i, idxs2@..]) => {
                tag = ts.get(*i as usize).expect("effective_tag: index oob of struct");
                idxs = idxs2;
            }
            (ast::Ty::Array(_, t), [_, idxs2@..]) => {
                // Don't check if OOB!
                tag = &*t;
                idxs = idxs2;
            }
            (ast::Ty::Named(id), _) => {
                tag = &named_types[id];
            }
            _ => panic!("effective_tag: index into non-empty aggregate"),
        }
    }
    tag.clone()
}

fn gep_idxs(p: &[Idx], idxs: &[Idx]) -> Vec<Idx> {
    let (i, ps) = p.split_last().expect("gep_idxs: invalid indices");
    let (j, idxs) = idxs.split_first().expect("gep_idxs: invalid indices");
    ps.iter().copied()
        .chain(std::iter::once(i + j))
        .chain(idxs.iter().copied()).collect()
}

// direct port: this is so annoying looking :(
fn legal_gep(named_types: &HashMap<ast::Tid, ast::Ty>, sty: &ast::Ty, tag: &ast::Ty) -> bool {
    fn ptrtoi8(named_types: &HashMap<ast::Tid, ast::Ty>, ty: &ast::Ty) -> ast::Ty {
        match ty {
            ast::Ty::Ptr(_) => ast::Ty::Ptr(Box::new(ast::Ty::I8)),
            ast::Ty::Struct(ts) => ast::Ty::Struct(ts.iter().map(|t| ptrtoi8(named_types, t)).collect()),
            ast::Ty::Array(n, t) => ast::Ty::Array(*n, Box::new(ptrtoi8(named_types, t))),
            ast::Ty::Named(id) => ptrtoi8(named_types, &named_types[id]),
            t => t.clone(),
        }
    }
    fn flatten_ty<'a>(named_types: &'a HashMap<ast::Tid, ast::Ty>, ty: &'a ast::Ty, b: &mut Vec<&'a ast::Ty>) {
        match ty {
            ast::Ty::Struct(ts) => {
                for t in ts {
                    flatten_ty(named_types, t, b);
                }
            }
            t => b.push(t),
        }
    }

    let mut styb = vec![];
    let mut tagb = vec![];
    let styi8 = ptrtoi8(named_types, &sty);
    let tagi8 = ptrtoi8(named_types, &tag);
    flatten_ty(named_types, &styi8, &mut styb);
    flatten_ty(named_types, &tagi8, &mut tagb);

    if tagb.len() < styb.len() {
        return false;
    }

    Iterator::eq(styb.iter(), tagb.iter().take(styb.len()))
}

fn gep_ptr(named_types: &HashMap<ast::Tid, ast::Ty>, ot: &ast::Ty, p: &Ptr, idxs: &[Idx]) -> SVal {
    if !legal_gep(named_types, ot, &effective_tag(named_types, p)) {
        return SVal::Undef;
    }

    match p {
        Ptr { bid: Bid::NullId, .. } => SVal::Undef,
        Ptr { ty, bid, indices } => SVal::Ptr(Ptr {
            ty: ty.clone(),
            bid: bid.clone(),
            indices: gep_idxs(indices, idxs),
        }),
    }
}
