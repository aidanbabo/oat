// todo: figure out references and stuff like what the hell ?!?
// todo: type interning
// on both of the above:
//      interning types would be the way to go in terms of actually having a real memory savings
//      i tried to introduce a 'prog to any type referencing something living in the ast::Prog
//      but this turned out to introduce more harm than good.
//      while the program cannot create types at runtime, we do inside of the interpreter
//      a good example of this is that for load and store instructions we only actually keep one
//      of the types parsed, so we create the other dynamically at runtime and pass it to operand
//      evaluation functions. This works out find in the case of the load, as we store the pointer
//      type and can just deref to get the pointee, but for stores we store the pointee type so we
//      have to use a box and create a new type. This is even worse for function types as we don't
//      have the type available when we parse and will always have to create it.

use internment::ArenaIntern;

use std::collections::{HashMap, BTreeMap};
use std::{fmt, ops};

use super::ast;

type Mid = i64; // memory block id
type Fid = i64; // stack frame id
type Idx = i64; // index

#[derive(Clone, Copy, Debug, PartialEq)]
enum Bid<'a> {
    Global(ast::Gid<'a>),
    Heap(Mid),
    Stack(Fid),
    Null,
}

impl<'a> fmt::Display for Bid<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bid::Global(gid) => write!(f, "@{gid}"),
            Bid::Heap(mid) => write!(f, "M{mid}"),
            Bid::Stack(fid) => write!(f, "S{fid}"),
            Bid::Null => write!(f, "null"),
        }
    }
}

#[derive(Clone, Debug)]
struct Ptr<'a> {
    ty: ast::Ty<'a>,
    bid: Bid<'a>,
    indices: Vec<Idx>, 
}

impl<'a> fmt::Display for Ptr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} ", self.ty, self.bid)?;
        super::print::write_separated(f, ", ", &self.indices)?;
        Ok(())
    }
}

// stack value
#[derive(Clone, Debug)]
enum SVal<'a> {
    Undef,
    Int(i64),
    Ptr(Ptr<'a>),
}

impl<'a> fmt::Display for SVal<'a> {
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
enum MTree<'a> {
    Word(SVal<'a>),
    Str(String),
    Node(MVal<'a>),
}

impl<'a> fmt::Display for MTree<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MTree::Word(sv) => write!(f, "{sv}"),
            MTree::Str(s) => write!(f, "\"{s}\""),
            MTree::Node(m) => write!(f, "{m}"),
        }
    }
}

#[derive(Clone, Debug)]
struct MVal<'a>(Vec<MTree<'a>>);

impl<'a> fmt::Display for MVal<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        super::print::write_separated(f, " ", &self.0)?;
        write!(f, "]")
    }
}


#[derive(Clone, Debug)]
struct Locals<'a>(HashMap<ast::Uid<'a>, SVal<'a>>);

impl<'a> ops::Deref for Locals<'a> {
    type Target = HashMap<ast::Uid<'a>, SVal<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> ops::DerefMut for Locals<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a> fmt::Display for Locals<'a> {
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

struct Config<'a> {
    globals: HashMap<ast::Gid<'a>, MVal<'a>>,
    heap: HashMap<Mid, MVal<'a>>,
    // basically a stack but with fast lookup, fids are always increasing
    stack: BTreeMap<Fid, MVal<'a>>,
}

// this always adds a lists worth of indirection, why?
fn mval_of_gdecl<'a>(gd: &ast::Gdecl<'a>) -> MVal<'a> {
    fn mtree_of_gdecl<'a>(gd: &ast::Gdecl<'a>) -> MTree<'a> {
        match gd {
            (ty, ast::Ginit::Null) => MTree::Word(SVal::Ptr(Ptr {
                ty: ty.clone(),
                bid: Bid::Null,
                indices: vec![0],
            })),
            (ty, ast::Ginit::Gid(g)) => MTree::Word(SVal::Ptr(Ptr {
                ty: ty.clone(),
                bid: Bid::Global(*g),
                indices: vec![0],
            })),
            (_, ast::Ginit::Bitcast(t1, v, _)) => mtree_of_gdecl(&(t1.clone(), (**v).clone())),
            (_, ast::Ginit::Int(i)) => MTree::Word(SVal::Int(*i)),
            (_, ast::Ginit::String(s)) => MTree::Str(s.clone()),
            (_, ast::Ginit::Array(gs) | ast::Ginit::Struct(gs)) => MTree::Node(MVal(gs.iter().map(mtree_of_gdecl).collect())),
        }
    }
    MVal(vec![mtree_of_gdecl(gd)])
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
    /// (unused)
    #[error("undefined memory dereference")]
    UndefMemDeref,
    /// uninitialized memory load
    #[error("uninitialized memory load")]
    UninitMemLoad,
    /// deref freed stack/heap memory
    #[error("use after free")]
    UseAfterFree,
}

const RUNTIME_FUNCTIONS: &[&str] = &["ll_puts", "ll_strcat", "ll_ltoa"];

struct Interpreter<'prog> {
    prog: &'prog ast::Prog<'prog>,
    config: Config<'prog>,
    id: i64,
    init_args: Vec<SVal<'prog>>,
}

impl<'prog> Interpreter<'prog> {

    fn new(prog: &'prog ast::Prog, args: &[&str]) -> Self {
        let mut interp = Interpreter {
            prog,
            config: Config {
                globals: prog.gdecls.iter().map(|(g, gd)| (*g, mval_of_gdecl(gd))).collect(),
                heap: Default::default(),
                stack: Default::default(),
            },
            id: 0,
            init_args: Default::default(),
        };

        let mut args: Vec<_> = args.to_vec();
        args.insert(0, "LLINTERP");
        let (ptrs, mut heap): (Vec<_>, HashMap<_, _>) = args.iter().map(|a| {
            let id = interp.next_id();
            let ptr = SVal::Ptr(Ptr {
                ty: ast::Ty::I8,
                bid: Bid::Heap(id),
                indices: vec![0],
            });
            (ptr, (id, MVal(vec![MTree::Str(a.to_string())])))
        }).unzip();

        let argc = SVal::Int(args.len() as i64);
        let aid = interp.next_id();
        let argv = SVal::Ptr(Ptr {
            ty: ast::Ty::Array(args.len() as i64, Box::new(ast::Ty::Ptr(Box::new(ast::Ty::I8)))),
            bid: Bid::Heap(aid),
            indices: vec![0, 0],
        });
        let amval: Vec<_> = ptrs.into_iter().map(MTree::Word).collect();
        heap.insert(aid, MVal(vec![MTree::Node(MVal(amval))]));

        interp.config.heap.extend(heap);
        interp.init_args = vec![argc, argv];
        interp
    }

    fn next_id(&mut self) -> i64 {
        self.id += 1;
        self.id
    }

    fn effective_type(&self, t: &ast::Ty<'prog>) -> ast::Ty<'prog> {
        if let ast::Ty::Named(id) = t {
            self.effective_type(&self.prog.tdecls[id])
        } else {
            t.clone()
        }
    }

    fn interp_bop(b: ast::Bop, v1: SVal<'prog>, v2: SVal<'prog>) -> SVal<'prog> {
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

    fn interp_cnd(c: ast::Cnd, v1: SVal<'prog>, v2: SVal<'prog>) -> SVal<'prog> {
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

    fn load_idxs(mut m: &MVal<'prog>, mut idxs: &[Idx]) -> Result<MTree<'prog>, ExecError> {

        if idxs.is_empty() {
            return Ok(MTree::Node(m.clone()));
        }

        loop {
            let (i, idxs2) = idxs.split_first().unwrap();
            idxs = idxs2;

            if *i < 0 || m.0.len() <= *i as usize {
                return Err(ExecError::OOBIndexDeref);
            }

            match (idxs, &m.0[*i as usize]) {
                ([], mt) => return Ok(mt.clone()),
                ([0], MTree::Str(s)) => return Ok(MTree::Str(s.clone())),
                (_, MTree::Word(_)) => panic!("load idxs: attempted to index into word"),
                (_, MTree::Str(_)) => panic!("load idxs: attempted to index into str"),
                (_, MTree::Node(m2)) => {
                    m = m2;
                }
            }
        }
    }

    // this function looks a little weird, I would like to write it
    // with a loop and not a fold, but the borrow checker better understands
    // functions/closures than loop iterations, so this is what we are left with
    fn store_idxs(m: &mut MVal<'prog>, idxs: &[Idx], mt: &MTree<'prog>) -> Result<(), ExecError> {
        if idxs.is_empty() {
            return Ok(());
        }

        let last_index = idxs.len() - 1;
        idxs.iter().enumerate().try_fold(m, |m, (iter_idx, i)| {
            if *i < 0 || *i > m.0.len() as i64 {
                return Err(ExecError::OOBIndexDeref);
            }
            let i = *i as usize;

            if iter_idx == last_index {
                m.0[i] = mt.clone();
                return Ok(m);
            }

            match &mut m.0[i] {
                MTree::Word(_) => panic!("load idxs: attempted to index into word"),
                MTree::Str(_) => panic!("load idxs: attempted to index into str"),
                MTree::Node(m) => Ok(m),
            }
        })?;

        Ok(())
    }

    fn load_bid(&self, bid: &Bid<'prog>) -> Result<&MVal<'prog>, ExecError> {
        match bid {
            Bid::Null => Err(ExecError::NullPtrDeref),
            Bid::Heap(mid) => self.config.heap.get(mid).ok_or(ExecError::UseAfterFree),
            Bid::Global(gid) => Ok(self.config.globals.get(gid).expect("Load: bogus gid")),
            Bid::Stack(fid) => self.config.stack.get(fid).ok_or(ExecError::UseAfterFree),
        }
    }

    fn load_ptr(&self, p: &Ptr<'prog>) -> Result<MTree<'prog>, ExecError> {
        Self::load_idxs(self.load_bid(&p.bid)?, &p.indices)
    }

    fn store_ptr(&mut self, p: &Ptr<'prog>, mt: &MTree<'prog>) -> Result<(), ExecError> {
        let mut mval = self.load_bid(&p.bid)?.clone();
        match p.bid {
            Bid::Null => Err(ExecError::NullPtrDeref),
            Bid::Heap(mid) => {
                Self::store_idxs(&mut mval, &p.indices, mt)?;
                self.config.heap.insert(mid, mval);
                Ok(())
            }
            Bid::Global(gid) => {
                Self::store_idxs(&mut mval, &p.indices, mt)?;
                self.config.globals.insert(gid, mval);
                Ok(())
            }
            Bid::Stack(fid) => {
                Self::store_idxs(&mut mval, &p.indices, mt)?;
                self.config.stack.insert(fid, mval);
                Ok(())
            }
        }
    }

    // Tag and GEP implementation
    fn effective_tag(&self, p: &Ptr<'prog>) -> ast::Ty<'prog> {
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
                    tag = t;
                    idxs = idxs2;
                }
                (ast::Ty::Named(id), _) => {
                    tag = &self.prog.tdecls[id];
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
    fn legal_gep(&self, sty: &ast::Ty<'prog>, tag: &ast::Ty<'prog>) -> bool {
        fn ptrtoi8<'a>(named_types: &HashMap<ast::Tid<'a>, ast::Ty<'a>>, ty: &ast::Ty<'a>) -> ast::Ty<'a> {
            match ty {
                ast::Ty::Ptr(_) => ast::Ty::Ptr(Box::new(ast::Ty::I8)),
                ast::Ty::Struct(ts) => ast::Ty::Struct(ts.iter().map(|t| ptrtoi8(named_types, t)).collect()),
                ast::Ty::Array(n, t) => ast::Ty::Array(*n, Box::new(ptrtoi8(named_types, t))),
                ast::Ty::Named(id) => ptrtoi8(named_types, &named_types[id]),
                t => t.clone(),
            }
        }
        fn flatten_ty<'a, 'p>(ty: &'a ast::Ty<'p>, b: &mut Vec<&'a ast::Ty<'p>>) {
            match ty {
                ast::Ty::Struct(ts) => {
                    for t in ts {
                        flatten_ty(t, b);
                    }
                }
                t => b.push(t),
            }
        }

        let mut styb = vec![];
        let mut tagb = vec![];
        let styi8 = ptrtoi8(&self.prog.tdecls, sty);
        let tagi8 = ptrtoi8(&self.prog.tdecls, tag);
        flatten_ty(&styi8, &mut styb);
        flatten_ty(&tagi8, &mut tagb);

        if tagb.len() < styb.len() {
            return false;
        }

        Iterator::eq(styb.iter(), tagb.iter().take(styb.len()))
    }

    fn gep_ptr(&self, ot: &ast::Ty<'prog>, p: &Ptr<'prog>, idxs: &[Idx]) -> SVal<'prog> {
        if !self.legal_gep(ot, &self.effective_tag(p)) {
            return SVal::Undef;
        }

        match p {
            Ptr { bid: Bid::Null, .. } => SVal::Undef,
            Ptr { ty, bid, indices } => SVal::Ptr(Ptr {
                ty: ty.clone(),
                bid: *bid,
                indices: Self::gep_idxs(indices, idxs),
            }),
        }
    }

    fn interp_operand(&self, locals: &Locals<'prog>, ty: &ast::Ty<'prog>, o: ast::Operand<'prog>) -> SVal<'prog> {
        match (ty, o) {
            (ast::Ty::I64, ast::Operand::Const(i)) |
            (ast::Ty::I1, ast::Operand::Const(i)) => SVal::Int(i),
            (ast::Ty::Ptr(ty), ast::Operand::Null) => SVal::Ptr(Ptr {
                ty: (**ty).clone(),
                bid: Bid::Null,
                indices: vec![0],
            }),
            (ast::Ty::Ptr(ty), ast::Operand::Gid(g)) => SVal::Ptr(Ptr {
                ty: (**ty).clone(),
                bid: Bid::Global(g),
                indices: vec![0],
            }),
            (_, ast::Operand::Id(u)) => locals[&u].clone(),
            (ast::Ty::Named(id), o) => self.interp_operand(locals, &self.prog.tdecls[id], o),
            _ => panic!("interp operand: malformed operand {o:?}:{ty:?}"),
        }
    }

    fn runtime_call(&mut self, ty: &ast::Ty<'prog>, func: ast::Gid<'prog>, args: &[SVal<'prog>]) -> Result<SVal<'prog>, ExecError> {
        let load_strptr = |p: &Ptr| if let MTree::Str(s) = self.load_ptr(p)? {
            Ok(s)
        } else {
            panic!("runtime_call: non-string ptr arg")
        };

        fn null_terminated_to_rust(s: &str) -> &str {
            let Some(end) = s.char_indices().find_map(|(i, c)| (c == '\0').then_some(i)) else {
                panic!("runtime_call: got a non-null-terminated string")
            };
            &s[..end]
        }

        match (ty, func.into_ref(), args) {
            (ast::Ty::Void, "ll_puts", [SVal::Ptr(p)]) => {
                let nt = load_strptr(p)?;
                let s = null_terminated_to_rust(&nt);
                println!("{}", s);
                Ok(SVal::Undef)
            }
            (ast::Ty::Ptr(t), "ll_strcat", [SVal::Ptr(ps1), SVal::Ptr(ps2)]) => {
                let nt1 = load_strptr(ps1)?;
                let nt2 = load_strptr(ps2)?;
                let s1 = null_terminated_to_rust(&nt1);
                let s2 = null_terminated_to_rust(&nt2);
                let mid = self.next_id();
                let mv = MVal(vec![MTree::Str(format!("{s1}{s2}\0"))]);
                self.config.heap.insert(mid, mv);
                Ok(SVal::Ptr(Ptr {
                    ty: (**t).clone(),
                    bid: Bid::Heap(mid),
                    indices: vec![0],
                }))

            }
            (ast::Ty::I64, "ll_ltoa", [SVal::Int(i)]) => {
                let mid = self.next_id();
                let mv = MVal(vec![MTree::Str(i.to_string())]);
                self.config.heap.insert(mid, mv);
                Ok(SVal::Ptr(Ptr {
                    ty: ty.clone(),
                    bid: Bid::Heap(mid),
                    indices: vec![0],
                }))
            }
            _ => panic!("runtime_call: invalid call to {func}"),
        }
    }

    fn interp_call(&mut self, ty: &ast::Ty<'prog>, func_name: ast::Gid<'prog>, args: &[SVal<'prog>]) -> Result<SVal<'prog>, ExecError> {
        if RUNTIME_FUNCTIONS.contains(&func_name.into_ref()) {
            return self.runtime_call(ty, func_name, args);
        }

        let (_, func) = self.prog.fdecls.iter().find(|f| f.0 == func_name).unwrap_or_else(|| panic!("interp_call: undefined function {func_name}"));

        if func.params.len() != args.len() {
            panic!("interp_call: wrong no. arguments for {func_name}");
        }

        let locals = Locals(func.params.iter().cloned().zip(args.iter().cloned()).collect());
        let id = self.next_id();
        // since we always use a higher id, this is effectivly pushing it to the stack
        self.config.stack.insert(id, MVal(vec![]));
        self.interp_cfg(&func.cfg, locals)
    }

    fn interp_insns(&mut self, locs: &mut Locals<'prog>, insns: &[(ast::Uid<'prog>, ast::Insn<'prog>)]) -> Result<(), ExecError> {
        for insn in insns {
            let (u, insn) = insn;
            match (*u, insn) {
                (u, ast::Insn::Binop(b, t, o1, o2)) => {
                    let v1 = self.interp_operand(locs, t, *o1);
                    let v2 = self.interp_operand(locs, t, *o2);
                    let vr = Self::interp_bop(*b, v1, v2);
                    locs.insert(u, vr);
                }
                (u, ast::Insn::Icmp(cnd, t, o1, o2)) => {
                    let v1 = self.interp_operand(locs, t, *o1);
                    let v2 = self.interp_operand(locs, t, *o2);
                    let vr = Self::interp_cnd(*cnd, v1, v2);
                    locs.insert(u, vr);
                }
                (u, ast::Insn::Alloca(ty)) => {
                    let mut entry = self.config.stack.last_entry().expect("stack empty");
                    let ptr = SVal::Ptr(Ptr {
                        ty: ty.clone(),
                        bid: Bid::Stack(*entry.key()),
                        indices: vec![entry.get().0.len() as i64],
                    });
                    entry.get_mut().0.push(MTree::Word(SVal::Undef));
                    locs.insert(u, ptr);
                }
                (u, ast::Insn::Load(t, o)) => {
                    let mt = match self.interp_operand(locs, &ast::Ty::Ptr(Box::new(t.clone())), *o) {
                        SVal::Ptr(p) => {
                            if self.effective_type(&self.effective_tag(&p)) != self.effective_type(t) {
                                return Err(ExecError::IncompatTagDeref);
                            }
                            self.load_ptr(&p)?
                        }
                        SVal::Undef => return Err(ExecError::UndefPtrDeref),
                        SVal::Int(_) => panic!("non-ptr arg for load"),
                    };
                    let v = match mt {
                        MTree::Word(SVal::Undef) => return Err(ExecError::UninitMemLoad),
                        MTree::Word(v) => v,
                        _ => panic!("load: returned aggregate"),
                    };
                    locs.insert(u, v);
                }
                (_, ast::Insn::Store(t, os, od)) => {
                    let vs = self.interp_operand(locs, t, *os);
                    let vd = self.interp_operand(locs, &ast::Ty::Ptr(Box::new(t.clone())), *od);
                    match vd {
                        SVal::Ptr(p) => {
                            if self.effective_type(&self.effective_tag(&p)) != self.effective_type(t) {
                                return Err(ExecError::IncompatTagDeref);
                            }
                            self.store_ptr(&p, &MTree::Word(vs))?
                        }
                        SVal::Undef => return Err(ExecError::UndefPtrDeref),
                        SVal::Int(_) => panic!("non-ptr arg for load"),
                    };
                }
                (u, ast::Insn::Call(t, ofn, ato)) => {
                    let ats: Vec<_> = ato.iter().map(|(t, _)| t.clone()).collect();
                    let ft = ast::Ty::Ptr(Box::new(ast::Ty::Fun(ats, Box::new(t.clone()))));
                    let g = match self.interp_operand(locs, &ft, *ofn) {
                        SVal::Ptr(Ptr { bid: Bid::Global(g), indices, ..}) if indices == [0] => g,
                        _ => panic!("bad call arg"),
                    };
                    let args: Vec<_> = ato.iter().map(|(t, o)| self.interp_operand(locs, t, *o)).collect();
                    let r = self.interp_call(t, g, &args)?;
                    locs.insert(u, r);
                }
                (u, ast::Insn::Bitcast(t1, o, _)) => {
                    let v = self.interp_operand(locs, t1, *o);
                    locs.insert(u, v);
                }
                (u, ast::Insn::Gep(t, o, os)) => {
                    let idxs: Vec<_> = os.iter()
                        .map(|o| self.interp_operand(locs, &ast::Ty::I64, *o))
                        .map(|sval| {
                            if let SVal::Int(i) = sval {
                                i
                            } else {
                                panic!("idx_of_sval: non-integer value")
                            }
                        }).collect();
                    let v = match self.interp_operand(locs, &ast::Ty::Ptr(Box::new(t.clone())), *o) {
                        SVal::Ptr(p) => self.gep_ptr(t, &p, &idxs),
                        SVal::Undef => SVal::Undef,
                        SVal::Int(_) => panic!("non-ptr arg for gep {t:?}"),
                    };
                    locs.insert(u, v);
                }
            }
        }
        Ok(())
    }

    fn interp_cfg(&mut self, cfg: &ast::Cfg<'prog>, mut locs: Locals<'prog>) -> Result<SVal<'prog>, ExecError> {
        let mut block = &cfg.entry;
        loop {
            self.interp_insns(&mut locs, &block.insns)?;
            block = match &block.term {
                (_, ast::Terminator::Ret(_, None)) => {
                    self.config.stack.pop_last();
                    return Ok(SVal::Undef);
                }
                (_, ast::Terminator::Ret(t, Some(o))) => {
                    self.config.stack.pop_last();
                    return Ok(self.interp_operand(&locs, t, *o));
                }
                (_, ast::Terminator::Br(l)) => {
                    &cfg.blocks.iter().find(|b| &*b.0 == l.into_ref()).expect("no block found with label").1
                }
                (_, ast::Terminator::Cbr(o, l1, l2)) => {
                    let v = self.interp_operand(&locs, &ast::Ty::I1, *o);
                    let l = if Self::interp_i1(&v) { l1 } else { l2 };
                    &cfg.blocks.iter().find(|b| &*b.0 == l.into_ref()).expect("no block found with label").1
                }
            }
        }
    }
}

// hardcoded in i64 return value
pub fn interp_prog(prog: &ast::Prog, args: &[&str], entry: ArenaIntern<'_, str>) -> Result<i64, ExecError> {
    let mut interp = Interpreter::new(prog, args);
    let r = interp.interp_call(&ast::Ty::I64, entry, &interp.init_args.clone())?;

    if let SVal::Int(i) = r {
        Ok(i)
    } else {
        panic!("main should return an i64");
    }
}
