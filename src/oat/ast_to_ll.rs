use internment::Arena;
use internment::ArenaIntern;

use std::collections::HashMap;

use super::Node;
use super::typechecker;
use super::ast as oast;
use crate::llvm::ast as llast;
use crate::llvm::Interners;
use crate::StrInterner;

#[derive(Debug, Default, PartialEq)]
struct PartialBlock<'a> {
    label: Option<llast::Lbl>, 
    insns: Vec<(llast::Uid<'a>, llast::Insn<'a>)>, 
    term: Option<(llast::Uid<'a>, llast::Terminator<'a>)>,
}

struct FunContext<'oat, 'll> {
    // no name conflicts at this stage
    locals: HashMap<oast::Ident<'oat>, (llast::Uid<'ll>, llast::Ty)>,
    cfg: llast::Cfg<'ll>,
    current: PartialBlock<'ll>,
    ret_ty: llast::Ty,
}

impl<'oat, 'll> FunContext<'oat, 'll> {
    pub fn start_block(&mut self, lbl: llast::Lbl) {
        self.current.label = Some(lbl);
    }

    pub fn push_insn(&mut self, uid: llast::Uid<'ll>, insn: llast::Insn<'ll>) {
        if self.current.label.is_none() {
            panic!("inserting into block with no name")
        }
        self.current.insns.push((uid, insn));
    }

    pub fn terminate(&mut self, uid: llast::Uid<'ll>, term: llast::Terminator<'ll>) {
        if let Some(term) = self.current.term.replace((uid, term)) {
            panic!("block already terminated with {term:?}");
        }
        let PartialBlock { label, insns, term } = std::mem::take(&mut self.current);
        let block = llast::Block {
            insns,
            term: term.unwrap(),
        };

        self.cfg.blocks.push((label.expect("block given name"), block));
    }
}

fn tipe(interner: &mut StrInterner<llast::Tid>, ot: oast::Ty<'_>) -> llast::Ty {
    use oast::TyKind as TK;
    use llast::Ty as Lty;
    match ot.kind {
        TK::Void => Lty::Void,
        TK::Bool => Lty::I1,
        TK::Int => Lty::I64,
        TK::String => Lty::Ptr(Box::new(Lty::I8)),
        TK::Struct(name) => Lty::Ptr(Box::new(Lty::Named(interner.intern(&name)))),
        TK::Array(t) => Lty::Ptr(Box::new(Lty::Struct(vec![Lty::I64, Lty::Array(0, Box::new(tipe(interner, *t)))]))),
        TK::Fun(args, ret) => Lty::Ptr(Box::new(Lty::Fun(args.into_iter().map(|t| tipe(interner, t)).collect(), Box::new(tipe(interner, *ret))))),
    }
}

// too much OOP: the constructor is FUCKED because i need a full context to call methods, but i
// don't yet have one! fix this garbage!
// ideas!: 
//  - split out mutable and non-mutable data
//  - split out data that outlives the context and data that is temporary
pub struct Context<'oat, 'll> {
    llprog: llast::Prog<'ll>,
    globals: HashMap<oast::Ident<'oat>, (llast::Gid, llast::Ty)>,
    structs: HashMap<oast::Ident<'oat>, Vec<(llast::Ty, oast::Ident<'oat>)>>,
    sym_num: usize,
    // this is a hack just to get projections working, as they don't know the name of their own
    // struct
    // this is caused by the names for ll structs and oat structs to be in different arenas
    // a more straightforward and maybe better way would be to add the struct name to the ast node
    // during typechecking, but since it's only this cutout we'll keep type info out of the ast
    ll_to_oat_structs: HashMap<llast::Tid, oast::Ident<'oat>>,

    arena: &'ll Arena<str>,
    interners: Interners,
}

impl<'oat, 'll> Context<'oat, 'll> {
    pub fn new(tctx: typechecker::Context<'oat>, arena: &'ll Arena<str>, oat_arena: &'oat Arena<str>) -> Self {

        let mut interners = Interners::default();
        let structs: HashMap<_, _> = tctx.structs.into_iter().map(|(n, fs)| {
            let pairs = fs.into_iter().map(|(ty, n)| (tipe(&mut interners.types, ty), n)).collect();
            (n, pairs)
        }).collect();

        let mut ctx = Context {
            llprog: llast::Prog::default(),
            globals: Default::default(),
            sym_num: 0,
            ll_to_oat_structs: structs.keys().map(|oname| (interners.types.intern(oname), *oname)).collect(),
            structs,
            arena,
            interners,
        };

        ctx.llprog.edecls.push((ctx.interners.globals.intern("oat_assert_array_length"), llast::Ty::Fun(vec![llast::Ty::Ptr(Box::new(llast::Ty::I64)), llast::Ty::I64], Box::new(llast::Ty::Void))));
        ctx.llprog.edecls.push((ctx.interners.globals.intern("oat_alloc_array"), llast::Ty::Fun(vec![llast::Ty::I64], Box::new(llast::Ty::Ptr(Box::new(llast::Ty::I64))))));
        ctx.llprog.edecls.push((ctx.interners.globals.intern("oat_malloc"), llast::Ty::Fun(vec![llast::Ty::I64], Box::new(llast::Ty::Ptr(Box::new(llast::Ty::I64))))));
        for (name, ty) in typechecker::BUILTINS.iter() {
            let ty = tipe(&mut ctx.interners.types, ty.clone());
            let llast::Ty::Ptr(ty) = ty else { unreachable!() };
            let ll_name = ctx.interners.globals.intern(name);
            ctx.llprog.edecls.push((ll_name, (*ty).clone()));
            ctx.globals.insert(oat_arena.intern(name), (ll_name, *ty));
        }
        
        ctx
    }

    pub fn lower(mut self, oprog: oast::Prog<'oat>) -> llast::Prog<'ll> {
        for decl in &oprog {
            if let oast::Decl::Fun(f) = decl {
                self.add_function_to_globals(f);
            }
        }

        for decl in oprog {
            match decl {
                oast::Decl::Var(v) => self.global(v.t),
                oast::Decl::Fun(f) => self.function(f.t),
                oast::Decl::Type(t) => self.tipe_decl(t.t),
            }
        }

        let Interners {
            labels,
            types,
            globals,
        } = self.interners;
        self.llprog.tables = llast::LookupTables {
            labels: labels.complete(),
            types: types.complete(),
            globals: globals.complete(),
        };
        self.llprog
    }

    fn gensym(&mut self, s: &str) -> ArenaIntern<'ll, str> {
        let s = format!("{s}{}", self.sym_num);
        self.sym_num += 1;
        self.arena.intern_string(s)
    }

    fn genlbl(&mut self, s: &str) -> llast::Lbl {
        let s = format!("{s}{}", self.sym_num);
        self.sym_num += 1;
        self.interners.labels.intern_string(s)
    }

    fn gengbl(&mut self, s: &str) -> llast::Gid {
        let s = format!("{s}{}", self.sym_num);
        self.sym_num += 1;
        self.interners.globals.intern_string(s)
    }

    fn gexp(&mut self, exp: oast::Exp<'oat>, name: String) -> (llast::Ty, llast::Ginit) {
        let (ty, op) = match exp {
            oast::Exp::Null(t) => (tipe(&mut self.interners.types, t), llast::Ginit::Null),
            oast::Exp::Bool(b) => (llast::Ty::I1, llast::Ginit::Int(b as i64)),
            oast::Exp::Int(i) => (llast::Ty::I64, llast::Ginit::Int(i)),
            oast::Exp::Str(s) => self.global_string(&name, s.to_string()),
            oast::Exp::Id(id) => {
                let (_name, ty) = self.globals.get(&id).expect("global id");
                let ty = if let llast::Ty::Fun(..) = ty {
                    llast::Ty::Ptr(Box::new(ty.clone()))
                } else {
                    ty.clone()
                };
                (ty, llast::Ginit::Gid(self.interners.globals.intern(&id)))
            }
            oast::Exp::ArrElems(ty, els) => {
                let els: Vec<_> = els.into_iter().enumerate().map(|(i, e)| self.gexp(e.t, format!("{name}{i}"))).collect();
                let array_len = els.len() as i64;
                let elem_ty = tipe(&mut self.interners.types, ty);

                let tmp_ty = array_maker(elem_ty.clone(), array_len);
                let new_ty = array_maker(elem_ty.clone(), 0);

                let tmp_uid = self.gengbl(&format!("{name}_tmp"));
                let tmp_ginit = llast::Ginit::Struct(vec![(llast::Ty::I64, llast::Ginit::Int(array_len)), (llast::Ty::Array(array_len, Box::new(elem_ty)), llast::Ginit::Array(els))]);
                self.llprog.gdecls.push((tmp_uid, (tmp_ty.clone(), tmp_ginit)));

                (ptr_maker(new_ty.clone()), llast::Ginit::Bitcast(ptr_maker(tmp_ty), Box::new(llast::Ginit::Gid(tmp_uid)), ptr_maker(new_ty)))
            }
            oast::Exp::Struct(struct_name, mut inits) => {
                let fields = self.structs[&struct_name].clone();
                let struct_id = self.interners.types.intern(&struct_name);
                let struct_ty = llast::Ty::Named(struct_id);
                let ginits = fields.iter().map(|(ty, name)| {
                    let found_ix = inits.iter().position(|(n, _)| n == name).expect("ensured by typechecker");
                    let (_, exp) = inits.remove(found_ix);
                    let (_, init) = self.gexp(exp.t, format!("{struct_name}.{name}"));
                    (ty.clone(), init)
                }).collect();

                let struct_uid = self.gengbl(&name);
                self.llprog.gdecls.push((struct_uid, (struct_ty.clone(), llast::Ginit::Struct(ginits))));
                let struct_ptr_ty = ptr_maker(struct_ty.clone());
                (struct_ptr_ty, llast::Ginit::Gid(struct_uid))
            }
            _ => unreachable!(),
        };
        (ty, op)
    }

    fn global(&mut self, v: oast::Gdecl<'oat>) {
        let (ty, op) = self.gexp(v.init.t, v.name.to_string());
        let interned = self.interners.globals.intern(&v.name);
        self.llprog.gdecls.push((interned, (ty.clone(), op)));
        assert!(self.globals.insert(v.name, (interned, ty)).is_none());
    }

    fn global_string(&mut self, name: &str, mut s: String) -> (llast::Ty, llast::Ginit) {
        // oat strings are nul-terminated
        s.push('\0');
        let temp = self.gengbl(&format!("{name}_tmp"));
        let array_ty = llast::Ty::Array(s.len() as i64, Box::new(llast::Ty::I8));
        self.llprog.gdecls.push((temp, (array_ty.clone(), llast::Ginit::String(s))));

        let string_ty = llast::Ty::Ptr(Box::new(llast::Ty::I8));
        let bitcast = llast::Ginit::Bitcast(llast::Ty::Ptr(Box::new(array_ty)), Box::new(llast::Ginit::Gid(temp)), string_ty.clone());
        (string_ty, bitcast)
    }

    fn add_function_to_globals(&mut self, func: &oast::Fdecl<'oat>) {
        let ret_ty = tipe(&mut self.interners.types, func.ret_ty.clone());
        let (arg_tys, _): (Vec<_>, Vec<_>) = func.args.iter().cloned().map(|(t, n)| (tipe(&mut self.interners.types, t), n)).unzip();

        let ty_fun = llast::Ty::Fun(arg_tys, Box::new(ret_ty));
        assert!(self.globals.insert(func.name, (self.interners.globals.intern(&func.name), ty_fun)).is_none());
    }

    fn function(&mut self, func: oast::Fdecl<'oat>) {
        let ret_ty = tipe(&mut self.interners.types, func.ret_ty);
        let (arg_tys, oat_names): (Vec<_>, Vec<_>) = func.args.into_iter().map(|(t, n)| (tipe(&mut self.interners.types, t), n)).unzip();
        let fun_ty = llast::FunTy {
            params: arg_tys,
            ret: ret_ty,
        };

        let post_entry_lbl = self.interners.labels.intern("post_entry");

        let mut fun_ctx = FunContext {
            cfg: llast::Cfg {
                entry: llast::Block {
                    insns: Default::default(),
                    term: (self.gensym("_"), llast::Terminator::Br(post_entry_lbl)),
                },
                blocks: vec![],
            },
            locals: Default::default(),
            ret_ty: fun_ty.ret.clone(),
            current: Default::default(),
        };

        let mut ll_names = Vec::new();
        for (oat_name, ty) in oat_names.iter().copied().zip(fun_ty.params.iter()) {
            let uid = self.gensym(&oat_name);
            let ll_name = self.arena.intern(&oat_name);

            fun_ctx.cfg.entry.insns.push((uid, llast::Insn::Alloca(ty.clone())));
            fun_ctx.locals.insert(oat_name, (uid, ty.clone()));
            fun_ctx.cfg.entry.insns.push((self.gensym("_"), llast::Insn::Store(ty.clone(), llast::Operand::Id(ll_name), llast::Operand::Id(uid))));
            ll_names.push(ll_name);
        }

        fun_ctx.start_block(post_entry_lbl);

        let returns = self.block(&mut fun_ctx, func.body);

        assert!(returns, "proved by typechecker");
        assert_eq!(fun_ctx.current, Default::default());

        let fdecl = llast::Fdecl {
            ty: fun_ty,
            params: ll_names,
            cfg: fun_ctx.cfg,
        };

        self.llprog.fdecls.push((self.interners.globals.intern(&func.name), fdecl));
    }

    fn block(&mut self, fun_ctx: &mut FunContext<'oat, 'll>, body: oast::Block<'oat>) -> bool {
        let nstatements = body.len();
        for (i, stmt) in body.into_iter().enumerate() {
            if self.stmt(fun_ctx, stmt.t) {
                assert_eq!(i + 1, nstatements);
                return true;
            }
        }
        false
    }

    fn typecast(&mut self, fun_ctx: &mut FunContext<'oat, 'll>, src: llast::Ty, op: llast::Operand<'ll>, dst: llast::Ty) -> llast::Operand<'ll> {
        if src == dst {
            return op
        }

        let bitcast = self.gensym("coerce");
        fun_ctx.push_insn(bitcast, llast::Insn::Bitcast(src, op, dst.clone()));
        llast::Operand::Id(bitcast)
    }

    fn stmt(&mut self, fun_ctx: &mut FunContext<'oat, 'll>, stmt: oast::Stmt<'oat>) -> bool {
        match stmt {
            oast::Stmt::Assn(lhs, rhs) => {
                let (rhs_op, ty) = self.exp(fun_ctx, rhs.t);
                let (lhs_ptr_op, pointee_ty) = self.lhs(fun_ctx, lhs.t);
                let rhs_op = self.typecast(fun_ctx, ty, rhs_op, pointee_ty.clone());
                fun_ctx.push_insn(self.gensym("_"), llast::Insn::Store(pointee_ty, rhs_op, lhs_ptr_op));
                false
            },
            oast::Stmt::Decl(d) => {
                self.vdecl(fun_ctx, d);
                false
            },
            oast::Stmt::Ret(v) => {
                let ret_op = v.map(|v| {
                    let (op, ty) = self.exp(fun_ctx, v.t);
                    self.typecast(fun_ctx, ty, op, fun_ctx.ret_ty.clone())
                });
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Ret(fun_ctx.ret_ty.clone(), ret_op));
                true
            },
            oast::Stmt::Call(f, args) => {
                let uid = self.gensym("_");
                self.call(fun_ctx, f.t, args, uid);
                false
            }
            oast::Stmt::If(cnd, if_blk, else_blk) => {
                let (cnd_op, _ty) = self.exp(fun_ctx, cnd.t);
                let then_lbl = self.genlbl("then");
                let else_lbl = self.genlbl("else");
                let after_lbl = self.genlbl("after");
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Cbr(cnd_op, then_lbl, else_lbl));

                fun_ctx.start_block(then_lbl);
                let if_returns = self.block(fun_ctx, if_blk);
                if !if_returns {
                    fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(after_lbl));
                }

                fun_ctx.start_block(else_lbl);
                let else_returns = self.block(fun_ctx, else_blk);
                if !else_returns {
                    fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(after_lbl));
                }

                if !if_returns || !else_returns {
                    fun_ctx.start_block(after_lbl);
                }

                if_returns && else_returns
            }
            oast::Stmt::IfNull(ty, name, exp, if_blk, else_blk) => {
                let (cnd_op, cnd_ty) = self.exp(fun_ctx, exp.t);
                let null_check_uid = self.gensym("null_check");
                let null_check = llast::Insn::Icmp(llast::Cnd::Ne, cnd_ty.clone(), cnd_op, llast::Operand::Null);
                fun_ctx.push_insn(null_check_uid, null_check);

                let then_lbl = self.genlbl("then");
                let else_lbl = self.genlbl("else");
                let after_lbl = self.genlbl("after");
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Cbr(llast::Operand::Id(null_check_uid), then_lbl, else_lbl));

                fun_ctx.start_block(then_lbl);

                let llty = tipe(&mut self.interners.types, ty);
                let alloca_uid = self.gensym(&name);
                fun_ctx.cfg.entry.insns.push((alloca_uid, llast::Insn::Alloca(llty.clone())));
                fun_ctx.locals.insert(name, (alloca_uid, llty.clone()));
                let cnd_op = self.typecast(fun_ctx, cnd_ty, cnd_op, llty.clone());
                fun_ctx.push_insn(self.gensym("_"), llast::Insn::Store(llty, cnd_op, llast::Operand::Id(alloca_uid)));

                let if_returns = self.block(fun_ctx, if_blk);
                if !if_returns {
                    fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(after_lbl));
                }

                fun_ctx.start_block(else_lbl);
                let else_returns = self.block(fun_ctx, else_blk);
                if !else_returns {
                    fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(after_lbl));
                }

                if !if_returns || !else_returns {
                    fun_ctx.start_block(after_lbl);
                }

                if_returns && else_returns
            }
            oast::Stmt::For(vdecls, cnd, update, blk) => {
                // todo: infinite loop and return analysis buffs?
                let for_top_lbl = self.genlbl("for_top");
                let for_body_lbl = self.genlbl("for_body");
                let for_update_lbl = self.genlbl("for_update");
                let for_after_lbl = self.genlbl("after_for");

                for vd in vdecls {
                    self.vdecl(fun_ctx, vd);
                }
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(for_top_lbl));

                fun_ctx.start_block(for_top_lbl);
                let cnd_op = if let Some(cnd) = cnd {
                    let (cnd_op, _ty) = self.exp(fun_ctx, cnd.t);
                    cnd_op
                } else {
                    llast::Operand::Const(1)
                };
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Cbr(cnd_op, for_body_lbl, for_after_lbl));

                fun_ctx.start_block(for_body_lbl);
                self.block(fun_ctx, blk);
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(for_update_lbl));

                fun_ctx.start_block(for_update_lbl);
                let update_returns = if let Some(upd) = update {
                    self.stmt(fun_ctx, upd.t)
                } else {
                    false
                };
                if !update_returns {
                    fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(for_top_lbl));
                }

                fun_ctx.start_block(for_after_lbl);

                false
            }
            oast::Stmt::While(cnd, blk) => {
                let while_top_lbl = self.genlbl("while_top");
                let while_body_lbl = self.genlbl("while_body");
                let while_after_lbl = self.genlbl("while_after");
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(while_top_lbl));

                fun_ctx.start_block(while_top_lbl);
                let (cnd_op, _ty) = self.exp(fun_ctx, cnd.t);
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Cbr(cnd_op, while_body_lbl, while_after_lbl));

                fun_ctx.start_block(while_body_lbl);
                self.block(fun_ctx, blk);
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(while_top_lbl));

                fun_ctx.start_block(while_after_lbl);

                false
            }
        }
    }

    fn vdecl(&mut self, fun_ctx: &mut FunContext<'oat, 'll>, d: oast::Vdecl<'oat>) {
        let (exp_uid, ty) = self.exp(fun_ctx, d.exp.t);
        let alloca = llast::Insn::Alloca(ty.clone());
        let alloca_uid = self.gensym(&d.name);
        fun_ctx.cfg.entry.insns.push((alloca_uid, alloca));
        fun_ctx.locals.insert(d.name, (alloca_uid, ty.clone()));
        fun_ctx.push_insn(self.gensym("_"), llast::Insn::Store(ty.clone(), exp_uid, llast::Operand::Id(alloca_uid)));
    }

    fn exp(&mut self, fun_ctx: &mut FunContext<'oat, 'll>, exp: oast::Exp<'oat>) -> (llast::Operand<'ll>, llast::Ty) {
        let (op, ty): (llast::Operand, llast::Ty) = match exp {
            oast::Exp::Null(t) => (llast::Operand::Null, tipe(&mut self.interners.types, t)),
            oast::Exp::Bool(b) => (llast::Operand::Const(b as i64), llast::Ty::I1),
            oast::Exp::Int(n) => (llast::Operand::Const(n), llast::Ty::I64),
            oast::Exp::Str(s) => {
                let gid = self.gengbl("string");
                // fixme: don't use the literal "string" here but something more unique?
                // is it even a bug?
                let (ty, ginit) = self.global_string("string", s.to_string());
                self.llprog.gdecls.push((gid, (ty.clone(), ginit)));

                let ty = llast::Ty::Ptr(Box::new(llast::Ty::I8));
                let insn = llast::Insn::Load(ty.clone(), llast::Operand::Gid(gid));
                let uid = self.gensym("uid");
                fun_ctx.push_insn(uid, insn);
                (llast::Operand::Id(uid), ty)
            }
            oast::Exp::ArrElems(aty, els) => {
                let arr_el_ty = tipe(&mut self.interners.types, aty);
                let (array_op, array_ty, array_base_ty) = self.oat_alloc_array(fun_ctx, arr_el_ty.clone(), llast::Operand::Const(els.len() as i64));

                for (ix, el) in els.into_iter().enumerate() {
                    let (op, ty) = self.exp(fun_ctx, el.t);
                    let op = self.typecast(fun_ctx, ty, op, arr_el_ty.clone());
                    let ix_ptr_uid = self.gensym("ix");
                    let ix_ptr_insn = llast::Insn::Gep(array_base_ty.clone(), array_op, vec![llast::Operand::Const(0), llast::Operand::Const(1), llast::Operand::Const(ix as i64)]);
                    fun_ctx.push_insn(ix_ptr_uid, ix_ptr_insn);
                    fun_ctx.push_insn(self.gensym("_"), llast::Insn::Store(arr_el_ty.clone(), op, llast::Operand::Id(ix_ptr_uid)));
                }

                (array_op, array_ty)
            }
            oast::Exp::ArrLen(ty, len) => {
                let (op, _) = self.exp(fun_ctx, len.t);
                let ty = tipe(&mut self.interners.types, ty);
                let (array_op, array_ty, _) = self.oat_alloc_array(fun_ctx, ty, op);
                (array_op, array_ty)
            }
            oast::Exp::ArrInit(ty, len, name, init) => {
                // todo: use phi nodes? might make code cleaner
                let arr_el_ty = tipe(&mut self.interners.types, ty);

                // allocate array
                let (len_op, _) = self.exp(fun_ctx, len.t);
                let (array_op, array_ty, array_base_ty) = self.oat_alloc_array(fun_ctx, arr_el_ty.clone(), len_op);

                let init_top_lbl = self.genlbl("init_top");
                let init_body_lbl = self.genlbl("init_body");
                let init_after_lbl = self.genlbl("init_after");

                // set up index var
                let ix_alloca_uid = self.gensym("init_ix_alloca");
                fun_ctx.push_insn(ix_alloca_uid, llast::Insn::Alloca(llast::Ty::I64));
                let ix_alloca_op = llast::Operand::Id(ix_alloca_uid);
                fun_ctx.push_insn(self.gensym("_"), llast::Insn::Store(llast::Ty::I64, llast::Operand::Const(0), ix_alloca_op));
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(init_top_lbl));

                // exit condition
                fun_ctx.start_block(init_top_lbl);
                let ix_load_uid = self.gensym("init_ix_load");
                fun_ctx.push_insn(ix_load_uid, llast::Insn::Load(llast::Ty::I64, ix_alloca_op));
                let ix_load_op = llast::Operand::Id(ix_load_uid);
                let cnd_uid = self.gensym("init_ix_check");
                fun_ctx.push_insn(cnd_uid, llast::Insn::Icmp(llast::Cnd::Slt, llast::Ty::I64, ix_load_op, len_op));
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Cbr(llast::Operand::Id(cnd_uid), init_body_lbl, init_after_lbl));

                // init exp
                fun_ctx.start_block(init_body_lbl);
                fun_ctx.locals.insert(name, (ix_alloca_uid, llast::Ty::I64));
                let (e_op, e_ty) = self.exp(fun_ctx, init.t);
                let e_op = self.typecast(fun_ctx, e_ty, e_op, arr_el_ty.clone());
                let gep_uid = self.gensym("init_assn");
                fun_ctx.push_insn(gep_uid, llast::Insn::Gep(array_base_ty, array_op, vec![llast::Operand::Const(0), llast::Operand::Const(1), ix_load_op]));
                fun_ctx.push_insn(self.gensym("_"), llast::Insn::Store(arr_el_ty, e_op, llast::Operand::Id(gep_uid)));

                // update
                let update_uid = self.gensym("init_ix_update");
                fun_ctx.push_insn(update_uid, llast::Insn::Binop(llast::Bop::Add, llast::Ty::I64, ix_load_op, llast::Operand::Const(1)));
                fun_ctx.push_insn(self.gensym("_"), llast::Insn::Store(llast::Ty::I64, llast::Operand::Id(update_uid), ix_alloca_op));
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(init_top_lbl));

                fun_ctx.start_block(init_after_lbl);

                (array_op, array_ty)
            }
            oast::Exp::Length(e) => {
                let (array_op, array_ty) = self.exp(fun_ctx, e.t);
                let llast::Ty::Ptr(array_base_ty) = array_ty else { unreachable!() };
                let gep = llast::Insn::Gep(*array_base_ty, array_op, vec![llast::Operand::Const(0), llast::Operand::Const(0)]);
                let len_ptr_uid = self.gensym("len_ptr");
                fun_ctx.push_insn(len_ptr_uid, gep);
                let uid = self.gensym("len");
                fun_ctx.push_insn(uid, llast::Insn::Load(llast::Ty::I64, llast::Operand::Id(len_ptr_uid)));
                (llast::Operand::Id(uid), llast::Ty::I64)
            }
            oast::Exp::Struct(struct_name, mut inits) => {
                let fields = self.structs[&struct_name].clone();
                let struct_id = self.interners.types.intern(&struct_name);
                let struct_base_ty = llast::Ty::Named(struct_id);
                let struct_ty = llast::Ty::Ptr(Box::new(struct_base_ty.clone()));

                let struct_size_bytes = fields.len() * 8;
                let (struct_storage_op_raw, malloc_ty) = self.call_internal(fun_ctx, "oat_malloc", &[llast::Operand::Const(struct_size_bytes as i64)]);
                let struct_uid = self.gensym("struct_ptr");
                fun_ctx.push_insn(struct_uid, llast::Insn::Bitcast(malloc_ty, struct_storage_op_raw, struct_ty.clone()));
                let struct_ptr = llast::Operand::Id(struct_uid);

                for (ix, (ty, name)) in fields.into_iter().enumerate() {
                    let found_ix = inits.iter().position(|(n, _)| n == &name).expect("ensured by typechecker");
                    let (_, exp) = inits.remove(found_ix);

                    let (op, init_ty) = self.exp(fun_ctx, exp.t);
                    let op = self.typecast(fun_ctx, init_ty, op, ty.clone());

                    let gep_uid = self.gensym(&format!("{struct_name}.{name}_init"));
                    fun_ctx.push_insn(gep_uid, llast::Insn::Gep(struct_base_ty.clone(), struct_ptr, vec![llast::Operand::Const(0), llast::Operand::Const(ix as i64)]));
                    fun_ctx.push_insn(self.gensym("_"), llast::Insn::Store(ty, op, llast::Operand::Id(gep_uid)));
                }

                (struct_ptr, struct_ty)
            }
            oast::Exp::Call(f, args) => {
                let uid = self.gensym("call");
                self.call(fun_ctx, f.t, args, uid)
            },
            oast::Exp::Bop(obop, lhs, rhs) => {
                let (op1, t1) = self.exp(fun_ctx, lhs.t);
                let (op2, t2) = self.exp(fun_ctx, rhs.t);
                let (t3, insn) = match obop {
                    oast::Binop::Add => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::Add, llast::Ty::I64, op1, op2)),
                    oast::Binop::Sub => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::Sub, llast::Ty::I64, op1, op2)),
                    oast::Binop::Mul => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::Mul, llast::Ty::I64, op1, op2)),
                    oast::Binop::Lt => (llast::Ty::I1, llast::Insn::Icmp(llast::Cnd::Slt, llast::Ty::I64, op1, op2)),
                    oast::Binop::Lte => (llast::Ty::I1, llast::Insn::Icmp(llast::Cnd::Sle, llast::Ty::I64, op1, op2)),
                    oast::Binop::Gt => (llast::Ty::I1, llast::Insn::Icmp(llast::Cnd::Sgt, llast::Ty::I64, op1, op2)),
                    oast::Binop::Gte => (llast::Ty::I1, llast::Insn::Icmp(llast::Cnd::Sge, llast::Ty::I64, op1, op2)),
                    oast::Binop::And => (llast::Ty::I1, llast::Insn::Binop(llast::Bop::And, llast::Ty::I1, op1, op2)),
                    oast::Binop::Or => (llast::Ty::I1, llast::Insn::Binop(llast::Bop::Or, llast::Ty::I1, op1, op2)),
                    oast::Binop::IAnd => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::And, llast::Ty::I64, op1, op2)),
                    oast::Binop::IOr => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::Or, llast::Ty::I64, op1, op2)),
                    oast::Binop::Shl => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::Shl, llast::Ty::I64, op1, op2)),
                    oast::Binop::Shr => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::Lshr, llast::Ty::I64, op1, op2)),
                    oast::Binop::Sar => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::Ashr, llast::Ty::I64, op1, op2)),
                    oast::Binop::Eq | oast::Binop::Neq => {
                        let op2 = self.typecast(fun_ctx, t2, op2, t1.clone());
                        let bop = if obop == oast::Binop::Eq {
                            llast::Cnd::Eq
                        } else {
                            llast::Cnd::Ne
                        };

                        (t1.clone(), llast::Insn::Icmp(bop, t1.clone(), op1, op2))
                    }
                };
                let uid = self.gensym("bop");
                fun_ctx.push_insn(uid, insn);
                (llast::Operand::Id(uid), t3)
            },
            oast::Exp::Uop(ouop, exp) => {
                let (e1, _t1) = self.exp(fun_ctx, exp.t);
                let (t2, insn) = match ouop {
                    oast::Unop::Neg => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::Sub, llast::Ty::I64, llast::Operand::Const(0), e1)),
                    oast::Unop::LogNot => (llast::Ty::I1, llast::Insn::Icmp(llast::Cnd::Eq, llast::Ty::I1, llast::Operand::Const(0), e1)),
                    oast::Unop::BitNot => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::Xor, llast::Ty::I64, llast::Operand::Const(-1), e1)),
                };
                let uid = self.gensym("uop");
                fun_ctx.push_insn(uid, insn);
                (llast::Operand::Id(uid), t2)
            }
            e@(oast::Exp::Id(..) | oast::Exp::Proj(..) | oast::Exp::Index(..)) => {
                let name = match &e {
                    oast::Exp::Id(id) => id.to_string(),
                    oast::Exp::Proj(_, field) => field.to_string(),
                    oast::Exp::Index(..) => "index".to_string(),
                    _ => unreachable!(),
                };

                let (ptr_operand, pointee_ty) = self.lhs(fun_ctx, e);
                if let llast::Ty::Fun(..) = &pointee_ty {
                    (ptr_operand, llast::Ty::Ptr(Box::new(pointee_ty)))
                } else {
                    let load_uid = self.gensym(&name);
                    let load_insn = llast::Insn::Load(pointee_ty.clone(), ptr_operand);
                    fun_ctx.push_insn(load_uid, load_insn);
                    (llast::Operand::Id(load_uid), pointee_ty.clone())
                }
            }
        };

        (op, ty)
    }

    fn oat_alloc_array(&mut self, fun_ctx: &mut FunContext<'oat, 'll>, ty: llast::Ty, len: llast::Operand<'ll>) -> (llast::Operand<'ll>, llast::Ty, llast::Ty) {
        let (i64_ptr_op, i64_ptr_ty) = self.call_internal(fun_ctx, "oat_alloc_array", &[len]);
        let array_uid = self.gensym("array");
        let array_base_ty = array_maker(ty, 0);
        let array_ty = ptr_maker(array_base_ty.clone());
        fun_ctx.push_insn(array_uid, llast::Insn::Bitcast(i64_ptr_ty, i64_ptr_op, array_ty.clone()));

        (llast::Operand::Id(array_uid), array_ty, array_base_ty)
    }

    fn call(&mut self, fun_ctx: &mut FunContext<'oat, 'll>, f: oast::Exp<'oat>, args: Vec<Node<oast::Exp<'oat>>>, uid: llast::Uid<'ll>) -> (llast::Operand<'ll>, llast::Ty) {
        let (fop, tf) = self.exp(fun_ctx, f);
        let llast::Ty::Ptr(p) = tf else { unreachable!() };
        let llast::Ty::Fun(arg_tys, ret_ty) = *p else { unreachable!() };
        let args: Vec<_> = args.into_iter().zip(arg_tys.iter()).map(|(a, arg_ty)| {
            let (op, t) = self.exp(fun_ctx, a.t);
            let op  = self.typecast(fun_ctx, t, op, arg_ty.clone());
            (arg_ty.clone(), op)
        }).collect();
        fun_ctx.push_insn(uid, llast::Insn::Call((*ret_ty).clone(), fop, args));
        (llast::Operand::Id(uid), *ret_ty)
    }

    /// will always return the storage slot
    fn lhs(&mut self, fun_ctx: &mut FunContext<'oat, 'll>, lhs: oast::Exp<'oat>) -> (llast::Operand<'ll>, llast::Ty) {
        match lhs {
            oast::Exp::Id(id) => {
                if let Some((ptr_uid, ty)) = fun_ctx.locals.get(&id) {
                    (llast::Operand::Id(*ptr_uid), ty.clone())
                } else if let Some((ptr_gid, ty)) = self.globals.get(&id) {
                    (llast::Operand::Gid(*ptr_gid), ty.clone())
                } else {
                    unreachable!()
                }
            }
            oast::Exp::Proj(exp, field_name) => {
                let (struct_op, struct_ty) = self.exp(fun_ctx, exp.t);
                let llast::Ty::Ptr(p) = &struct_ty else { unreachable!() };
                let struct_base_ty = *p.clone();
                let llast::Ty::Named(struct_id) = &struct_base_ty else { unreachable!() };
                let struct_name = self.ll_to_oat_structs[struct_id];
                let gep_uid = self.gensym(&format!("{struct_name}.{field_name}"));

                let fields = &self.structs[&struct_name];
                let index = fields.iter().position(|(_, n)| n == &field_name).unwrap();
                let (field_ty, _) = &fields[index];
                fun_ctx.push_insn(gep_uid, llast::Insn::Gep(struct_base_ty, struct_op, vec![llast::Operand::Const(0), llast::Operand::Const(index as i64)]));
                (llast::Operand::Id(gep_uid), field_ty.clone())
            }
            oast::Exp::Index(arr, ix) => {
                let (aop, aty) = self.exp(fun_ctx, arr.t);
                let (iop, _) = self.exp(fun_ctx, ix.t);

                let llast::Ty::Ptr(p) = &aty else { unreachable!() };
                let ptr_ty = p.clone();
                let llast::Ty::Struct(v) = &**p else { unreachable!() };
                let llast::Ty::Array(_, elem_ty) = &v[1] else { unreachable!() };
                let elem_ty: llast::Ty = *elem_ty.clone();

                let len_ptr = self.gensym("len");
                let len_ptr_insn = llast::Insn::Gep(*ptr_ty.clone(), aop, vec![llast::Operand::Const(0), llast::Operand::Const(0)]);
                fun_ctx.push_insn(len_ptr, len_ptr_insn);
                self.call_internal(fun_ctx, "oat_assert_array_length", &[llast::Operand::Id(len_ptr), iop]);

                let gep_uid = self.gensym("index");
                let gep = llast::Insn::Gep(*ptr_ty, aop, vec![llast::Operand::Const(0), llast::Operand::Const(1), iop]);
                fun_ctx.push_insn(gep_uid, gep);
                (llast::Operand::Id(gep_uid), elem_ty)
            }
            _ => unreachable!(),
        }
    }

    fn call_internal(&mut self, fun_ctx: &mut FunContext<'oat, 'll>, name: &'static str, args: &[llast::Operand<'ll>]) -> (llast::Operand<'ll>, llast::Ty) {
        let name = self.interners.globals.intern(name);
        let ret = self.gensym("ret");
        let (_, ty) = self.llprog.edecls.iter().find(|(n, _)| *n == name).expect("unknown builtin");
        let llast::Ty::Fun(arg_tys, ret_ty) = ty else { unreachable!() };
        let args: Vec<_> = args.iter().zip(arg_tys).map(|(a, t)| (t.clone(), *a)).collect();
        let ret_ty = (**ret_ty).clone();
        let insn = llast::Insn::Call(ret_ty.clone(), llast::Operand::Gid(name), args.to_vec());
        fun_ctx.push_insn(ret, insn);
        (llast::Operand::Id(ret), ret_ty)
    }

    fn tipe_decl(&mut self, t: oast::Tdecl) {
        let fields = self.structs[&t.name].iter().map(|(t, _)| t).cloned().collect();
        self.llprog.tdecls.insert(self.interners.types.intern(&t.name), llast::Ty::Struct(fields));
    }
}

fn array_maker(ty: llast::Ty, len: i64) -> llast::Ty {
    llast::Ty::Struct(vec![llast::Ty::I64, llast::Ty::Array(len, Box::new(ty))])
}

fn ptr_maker(ty: llast::Ty) -> llast::Ty {
    llast::Ty::Ptr(Box::new(ty))
}
