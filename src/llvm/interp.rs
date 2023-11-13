// todo: figure out references and stuff like what the hell ?!?

use std::collections::{HashMap, BTreeMap};
use std::{fmt, ops};

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
        write!(f, "{} {} ", self.ty, self.bid)?;
        let mut first = true;
        for idx in &self.indices {
            if first {
                write!(f, "{idx}")?
               } else {
                write!(f, ", {idx}")?
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


#[derive(Clone, Debug)]
struct Locals(HashMap<ast::Uid, SVal>);

impl ops::Deref for Locals {
    type Target = HashMap<ast::Uid, SVal>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ops::DerefMut for Locals {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl fmt::Display for Locals {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for (k, v) in &self.0 {
            if first {
                write!(f, "{k}: {v}")?;
            } else {
                write!(f, ", {k}: {v}")?;
            }
            first = false;
        }
        write!(f, "}}")
    }
}

#[derive(Clone)]
struct Config {
    globals: HashMap<ast::Gid, MVal>,
    heap: HashMap<Mid, MVal>,
    stack: BTreeMap<Fid, MVal>,
}

// this always adds a lists worth of indirection, why?
fn mval_of_gdecl(gd: &ast::Gdecl) -> MVal {
    fn mtree_of_gdecl(gd: &ast::Gdecl) -> MTree {
        match gd {
            (ty, ast::Ginit::Null) => MTree::Word(SVal::Ptr(Ptr {
                ty: ty.clone(),
                bid: Bid::NullId,
                indices: vec![0],
            })),
            (ty, ast::Ginit::Gid(g)) => MTree::Word(SVal::Ptr(Ptr {
                ty: ty.clone(),
                bid: Bid::GlobalId(g.clone()),
                indices: vec![0],
            })),
            (_, ast::Ginit::Bitcast(t1, v, _)) => mtree_of_gdecl(&(t1.clone(), (**v).clone())),
            (_, ast::Ginit::Int(i)) => MTree::Word(SVal::Int(*i)),
            (_, ast::Ginit::String(s)) => MTree::Str(s.clone()),
            (_, ast::Ginit::Array(gs) | ast::Ginit::Struct(gs)) => MTree::Node(MVal(gs.into_iter().map(mtree_of_gdecl).collect())),
        }
    }
    MVal(vec![mtree_of_gdecl(gd)])
}

// undef constructor
// used later? ported on hw3
#[allow(dead_code)]
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

#[derive(thiserror::Error, Debug)]
pub enum ExecError {
    /// mem access not in bounds
    #[error("out of bounds memory access")]
    OOBIndexDeref,
    /// deref Null
    #[error("null pointer dereference")]
    NullPtrDeref,
    /// deref Undef pointer (from bad GEP)
    #[error("undefined pointer dereference")]
    UndefPtrDeref,
    /// deref pointer at wrong type (bad bitcast)
    #[error("incompatible tag dereference")]
    IncompatTagDeref,
    /// read uninitialized memory
    #[error("undefined memory dereference")]
    UndefMemDeref,
    /// uninitialized memory load
    #[error("uninitialized memory load")]
    UninitMemLoad,
    /// deref freed stack/heap memory
    #[error("use after free")]
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
        SVal::Int(1) => true,
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
            if *i < 0 || m.0.len() <= *i as usize {
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

fn load_ptr(c: &Config, p: &Ptr) -> Result<MTree, ExecError> {
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

const RUNTIME_FUNCTIONS: &[&str] = &["ll_puts", "ll_strcat", "ll_ltoa"];

fn runtime_call(ty: &ast::Ty, func: &ast::Gid, args: &[SVal], config: &Config, next_id: &mut impl FnMut() -> i64) -> Result<(Config, SVal), ExecError> {
    let load_strptr = |p: &Ptr| if let MTree::Str(s) = load_ptr(config, p)? {
        Ok(s)
    } else {
        panic!("runtime_call: non-string ptr arg")
    };

    match (ty, &**func, args) {
        (ast::Ty::Void, "ll_puts", [SVal::Ptr(p)]) => {
            let s = load_strptr(p)?;
            println!("{s}");
            Ok((config.clone(), SVal::Undef))
        }
        (ast::Ty::Ptr(t), "ll_strcat", [SVal::Ptr(ps1), SVal::Ptr(ps2)]) => {
            let s1 = load_strptr(ps1)?;
            let s2 = load_strptr(ps2)?;
            let mid = next_id();
            let mv = MVal(vec![MTree::Str(format!("{s1}{s2}"))]);
            let mut new_config = config.clone();
            new_config.heap.insert(mid, mv);
            Ok((new_config, SVal::Ptr(Ptr {
                ty: (**t).clone(),
                bid: Bid::HeapId(mid),
                indices: vec![0],
            })))

        }
        (ast::Ty::I64, "ll_ltoa", [SVal::Int(i), SVal::Ptr(..)]) => {
            let mid = next_id();
            let mv = MVal(vec![MTree::Str(i.to_string())]);
            let mut new_config = config.clone();
            new_config.heap.insert(mid, mv);
            Ok((new_config, SVal::Ptr(Ptr {
                ty: ty.clone(),
                bid: Bid::HeapId(mid),
                indices: vec![0],
            })))
        }
        _ => panic!("runtime_call: invalid call to {func}"),
    }
}

fn interp_call(prog: &ast::Prog, ty: &ast::Ty, func_name: &ast::Gid, args: &[SVal], config: &Config, next_id: &mut impl FnMut() -> i64) -> Result<(Config, SVal), ExecError> {
    if RUNTIME_FUNCTIONS.contains(&&**func_name) {
        return runtime_call(ty, func_name, args, config, next_id);
    }

    let (_, func) = prog.fdecls.iter().find(|f| &f.0 == func_name).expect(&format!("interp_call: undefined function {func_name}"));

    if func.params.len() != args.len() {
        panic!("interp_call: wrong no. arguments for {func_name}");
    }

    let locals = Locals(func.params.iter().cloned().zip(args.iter().cloned()).collect());
    let mut new_config = config.clone();
    new_config.stack.insert(next_id(), MVal(vec![]));
    interp_cfg(prog, &func.cfg, &locals, &new_config, next_id)
}

// mutable args?
fn interp_cfg(prog: &ast::Prog, cfg: &ast::Cfg, locs: &Locals, config: &Config, next_id: &mut impl FnMut() -> i64) -> Result<(Config, SVal), ExecError> {
    let mut locs = locs.clone();
    let mut config = config.clone();

    let mut block = &cfg.entry;
    let mut insn_idx = 0;
    loop {
        let insn = block.insns.get(insn_idx);
        match (insn, &block.term) {
            (Some((u, ast::Insn::Binop(b, t, o1, o2))), _) => {
                let v1 = interp_operand(&prog.tdecls, &locs, t, o1);
                let v2 = interp_operand(&prog.tdecls, &locs, t, o2);
                let vr = interp_bop(*b, v1, v2);
                locs.insert(u.clone(), vr);
                insn_idx += 1;
            }
            (Some((u, ast::Insn::Icmp(cnd, t, o1, o2))), _) => {
                let v1 = interp_operand(&prog.tdecls, &locs, t, o1);
                let v2 = interp_operand(&prog.tdecls, &locs, t, o2);
                let vr = interp_cnd(*cnd, v1, v2);
                locs.insert(u.clone(), vr);
                insn_idx += 1;
            }
            (Some((u, ast::Insn::Alloca(ty))), _) => {
                let mut entry = config.stack.last_entry().expect("stack empty");
                let ptr = SVal::Ptr(Ptr {
                    ty: ty.clone(),
                    bid: Bid::StackId(*entry.key()),
                    indices: vec![entry.get().0.len() as i64],
                });
                entry.get_mut().0.push(MTree::Word(SVal::Undef));
                locs.insert(u.clone(), ptr);
                insn_idx += 1;
            }
            (Some((u, ast::Insn::Load(ast::Ty::Ptr(t), o))), _) => {
                let mt = match interp_operand(&prog.tdecls, &locs, &ast::Ty::Ptr(t.clone()), &o) {
                    SVal::Ptr(p) => {
                        if effective_type(&prog.tdecls, &effective_tag(&prog.tdecls, &p)) != effective_type(&prog.tdecls, &t) {
                            return Err(ExecError::IncompatTagDeref);
                        }
                        load_ptr(&config, &p)?
                    }
                    SVal::Undef => return Err(ExecError::UndefPtrDeref),
                    SVal::Int(_) => panic!("non-ptr arg for load"),
                };
                let v = match mt {
                    MTree::Word(SVal::Undef) => return Err(ExecError::UninitMemLoad),
                    MTree::Word(v) => v,
                    _ => panic!("load: returned aggregate"),
                };
                locs.insert(u.clone(), v);
                insn_idx += 1;
            }
            (Some((_, ast::Insn::Store(t, os, od))), _) => {
                let vs = interp_operand(&prog.tdecls, &locs, &t, &os);
                let vd = interp_operand(&prog.tdecls, &locs, &ast::Ty::Ptr(Box::new(t.clone())), &od);
                config = match vd {
                    SVal::Ptr(p) => {
                        if effective_type(&prog.tdecls, &effective_tag(&prog.tdecls, &p)) != effective_type(&prog.tdecls, &t) {
                            return Err(ExecError::IncompatTagDeref);
                        }
                        store_ptr(&config, &p, &MTree::Word(vs))?
                    }
                    SVal::Undef => return Err(ExecError::UndefPtrDeref),
                    SVal::Int(_) => panic!("non-ptr arg for load"),
                };
                insn_idx += 1;
            }
            (Some((u, ast::Insn::Call(t, ofn, ato))), _) => {
                let ats: Vec<_> = ato.iter().map(|(t, _)| t.clone()).collect();
                let ft = ast::Ty::Ptr(Box::new(ast::Ty::Fun(ats, Box::new(t.clone()))));
                let g = match interp_operand(&prog.tdecls, &locs, &ft, &ofn) {
                    SVal::Ptr(Ptr { bid: Bid::GlobalId(g), indices, ..}) if indices == &[0] => g,
                    _ => panic!("bad call arg"),
                };
                let args: Vec<_> = ato.iter().map(|(t, o)| interp_operand(&prog.tdecls, &locs, t, o)).collect();
                let (c, r) = interp_call(prog, t, &g, &args, &config, next_id)?;
                locs.insert(u.clone(), r);
                config = c;
                insn_idx += 1
            }
            (Some((u, ast::Insn::Bitcast(t1, o, _))), _) => {
                let v = interp_operand(&prog.tdecls, &locs, &t1, &o);
                locs.insert(u.clone(), v);
                insn_idx += 1;
            }
            (Some((u, ast::Insn::Gep(ty, o, os))), _) => {
                let t = dptr(&prog.tdecls, ty);
                let idxs: Vec<_> = os.iter()
                    .map(|o| interp_operand(&prog.tdecls, &locs, &ast::Ty::I64, o))
                    .map(|sval| {
                        if let SVal::Int(i) = sval {
                            i
                        } else {
                            panic!("idx_of_sval: non-integer value")
                        }
                    }).collect();
                let v = match interp_operand(&prog.tdecls, &locs, &ast::Ty::Ptr(Box::new(t.clone())), o) {
                    SVal::Ptr(p) => gep_ptr(&prog.tdecls, t, &p, &idxs),
                    SVal::Undef => SVal::Undef,
                    SVal::Int(_) => panic!("non-ptr arg for gep {t:?}"),
                };
                locs.insert(u.clone(), v);
                insn_idx += 1;
            }
            (None, (_, ast::Terminator::Ret(_, None))) => {
                config.stack.pop_last();
                return Ok((config, SVal::Undef));
            }
            (None, (_, ast::Terminator::Ret(t, Some(o)))) => {
                config.stack.pop_last();
                return Ok((config, interp_operand(&prog.tdecls, &locs, &t, &o)));
            }
            (None, (_, ast::Terminator::Br(l))) => {
                block = &cfg.blocks.iter().find(|b| &*b.0 == l).expect("no block found with label").1;
                insn_idx = 0;
            }
            (None, (_, ast::Terminator::Cbr(o, l1, l2))) => {
                let v = interp_operand(&prog.tdecls, &locs, &ast::Ty::I1, &o);
                let l = if interp_i1(&v) { l1 } else { l2 };
                block = &cfg.blocks.iter().find(|b| &*b.0 == l).expect("no block found with label").1;
                insn_idx = 0;
            }
            _ => panic!("invalid instructin"),
        }
    }

    fn dptr<'a>(named_types: &'a HashMap<ast::Tid, ast::Ty>, ty: &'a ast::Ty) -> &'a ast::Ty {
        match ty {
            ast::Ty::Ptr(t) => t,
            ast::Ty::Named(id) => dptr(named_types, &named_types[id]),
            _ => panic!("dptr: not a pointer type"),
        }
    }

    fn effective_type(named_types: &HashMap<ast::Tid, ast::Ty>, t: &ast::Ty) -> ast::Ty {
        if let ast::Ty::Named(id) = t {
            effective_type(named_types, &named_types[id])
        } else {
            t.clone()
        }
    }
}

// hardcoded in i64 return value
pub fn interp_prog(prog: &ast::Prog, args: &[&str]) -> Result<i64, ExecError> {
    let globals: HashMap<_, _> = prog.gdecls.iter().map(|(g, gd)| (g.clone(), mval_of_gdecl(gd))).collect();

    let mut id = 0i64;
    let mut next_id = move || {
        id += 1;
        id
    };

    let mut args: Vec<_> = args.iter().map(|s| *s).collect();
    args.insert(0, "LLINTERP");
    let (ptrs, mut heap): (Vec<_>, HashMap<_, _>) = args.iter().map(|a| {
        let id = next_id();
        let ptr = SVal::Ptr(Ptr {
            ty: ast::Ty::I8,
            bid: Bid::HeapId(id),
            indices: vec![0],
        });
        (ptr, (id, MVal(vec![MTree::Str(a.to_string())])))
    }).unzip();

    let argc = SVal::Int(args.len() as i64);
    let aid = next_id();
    let argv = SVal::Ptr(Ptr {
        ty: ast::Ty::Array(args.len() as i64, Box::new(ast::Ty::Ptr(Box::new(ast::Ty::I8)))),
        bid: Bid::HeapId(aid),
        indices: vec![0, 0],
    });
    let amval: Vec<_> = ptrs.into_iter().map(|p| MTree::Word(p)).collect();
    heap.insert(aid, MVal(vec![MTree::Node(MVal(amval))]));
    let config = Config {
        globals,
        heap,
        stack: Default::default(),
    };
    let (_, r) = interp_call(prog, &ast::Ty::I64, &"main".to_string(), &[argc, argv], &config, &mut next_id)?;
    if let SVal::Int(i) = r {
        Ok(i)
    } else {
        panic!("main should return an i64");
    }
}
