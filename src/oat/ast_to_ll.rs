use std::collections::HashMap;

use super::{ast as oast, Node};
use crate::llvm::ast as llast;

struct FunContext {
    locals: Vec<HashMap<oast::Ident, (llast::Uid, llast::Ty)>>,
    cfg: llast::Cfg,
    current: (Option<llast::Uid>, Vec<(llast::Uid, llast::Insn)>, Option<(llast::Uid, llast::Terminator)>),
    ret_ty: llast::Ty,
}

impl FunContext {
    pub fn start_block(&mut self, name: llast::Uid) {
        self.current.0 = Some(name);
    }

    pub fn push_insn(&mut self, uid: llast::Uid, insn: llast::Insn) {
        if self.current.0.is_none() {
            panic!("inserting into block with no name")
        }
        self.current.1.push((uid, insn));
    }

    pub fn terminate(&mut self, uid: llast::Uid, term: llast::Terminator) {
        if let Some(term) = self.current.2.replace((uid, term)) {
            panic!("block already terminated with {term:?}");
        }
        let (name, insns, term) = std::mem::take(&mut self.current);
        let block = llast::Block {
            insns,
            term: term.unwrap(),
        };

        self.cfg.blocks.push((name.expect("block given name"), block));
    }

    pub fn push_scope(&mut self) {
        self.locals.push(Default::default());
    }

    pub fn pop_scope(&mut self) {
        self.locals.pop();
    }

    pub fn add_local(&mut self, key: oast::Ident, val: (llast::Uid, llast::Ty)) {
        self.locals.last_mut().unwrap().insert(key, val);
    }

    pub fn lookup_local(&self, name: &oast::Ident) -> Option<&(String, llast::Ty)> {
        for scope in self.locals.iter().rev() {
            if let Some(val) = scope.get(name) {
                return Some(val);
            }
        }
        None
    }
}

pub struct Context {
    llprog: llast::Prog,
    globals: HashMap<oast::Ident, (llast::Gid, llast::Ty)>,
    sym_num: usize,
}

impl Context {
    pub fn new() -> Self {
        let mut ctx = Context {
            llprog: llast::Prog {
                tdecls: Default::default(),
                gdecls: Default::default(),
                fdecls: Default::default(),
                edecls: Default::default(),
            },
            globals: Default::default(),
            sym_num: 0,
        };

        let string_type = llast::Ty::Ptr(Box::new(llast::Ty::I8));
        let int_array_type = llast::Ty::Ptr(Box::new(array_maker(llast::Ty::I64, 0)));

        ctx.llprog.edecls.push(("oat_assert_array_length".to_string(), llast::Ty::Fun(vec![llast::Ty::Ptr(Box::new(llast::Ty::I64)), llast::Ty::I64], Box::new(llast::Ty::Void))));
        ctx.llprog.edecls.push(("oat_alloc_array".to_string(), llast::Ty::Fun(vec![llast::Ty::I64], Box::new(llast::Ty::Ptr(Box::new(llast::Ty::I64))))));
        ctx.add_builtin("print_string", llast::Ty::Fun(vec![string_type.clone()], Box::new(llast::Ty::Void)));
        ctx.add_builtin("print_int", llast::Ty::Fun(vec![llast::Ty::I64], Box::new(llast::Ty::Void)));
        ctx.add_builtin("array_of_string", llast::Ty::Fun(vec![string_type.clone()], Box::new(int_array_type.clone())));
        ctx.add_builtin("string_of_array", llast::Ty::Fun(vec![int_array_type], Box::new(string_type.clone())));
        ctx.add_builtin("string_of_int", llast::Ty::Fun(vec![llast::Ty::I64], Box::new(string_type)));
        
        ctx
    }

    fn add_builtin(&mut self, name: &'static str, ty: llast::Ty) {
        self.llprog.edecls.push((name.to_string(), ty.clone()));
        self.globals.insert(name.to_string(), (name.to_string(), ty));
    }

    // todo: order independent top level ?
    pub fn lower(mut self, oprog: oast::Prog) -> llast::Prog {
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

        self.llprog
    }

    fn gensym(&mut self, s: &str) -> String {
        let s = format!("_{s}{}", self.sym_num);
        self.sym_num += 1;
        s
    }

    fn make_global(&mut self, name: String, ty: llast::Ty, init: llast::Ginit) {
        self.llprog.gdecls.push((name.clone(), (ty.clone(), init)));
        assert!(self.globals.insert(name.clone(), (name, ty)).is_none());
    }

    fn gexp(&mut self, exp: oast::Exp, name: String) -> (llast::Ty, llast::Ginit) {
        let (ty, op) = match exp {
            oast::Exp::Null(t) => (tipe(t), llast::Ginit::Null),
            oast::Exp::Bool(b) => (llast::Ty::I1, llast::Ginit::Int(b as i64)),
            oast::Exp::Int(i) => (llast::Ty::I64, llast::Ginit::Int(i)),
            oast::Exp::Str(s) => self.global_string(name, s),
            oast::Exp::Id(id) => {
                let (_name, ty) = self.globals.get(&id).expect("global id");
                (ty.clone(), llast::Ginit::Gid(id))
            }
            oast::Exp::ArrElems(ty, els) => {
                let els: Vec<_> = els.into_iter().enumerate().map(|(i, e)| self.gexp(e.t, format!("{name}{i}"))).collect();
                let array_len = els.len() as i64;
                let elem_ty = tipe(ty);

                let tmp_ty = array_maker(elem_ty.clone(), array_len);
                let new_ty = array_maker(elem_ty.clone(), 0);

                let tmp_uid = self.gensym(&format!("{name}_tmp"));
                let tmp_ginit = llast::Ginit::Struct(vec![(llast::Ty::I64, llast::Ginit::Int(array_len)), (llast::Ty::Array(array_len, Box::new(elem_ty)), llast::Ginit::Array(els))]);
                self.make_global(tmp_uid.clone(), tmp_ty.clone(), tmp_ginit);

                (ptr_maker(new_ty.clone()), llast::Ginit::Bitcast(ptr_maker(tmp_ty), Box::new(llast::Ginit::Gid(tmp_uid)), ptr_maker(new_ty)))
            }
            _ => unreachable!(),
        };
        (ty, op)
    }

    fn global(&mut self, v: oast::Gdecl) {
        let (ty, op) = self.gexp(v.init.t, v.name.clone());
        self.llprog.gdecls.push((v.name.clone(), (ty.clone(), op)));
        assert!(self.globals.insert(v.name.clone(), (v.name, ty)).is_none());
    }

    fn global_string(&mut self, name: String, mut s: String) -> (llast::Ty, llast::Ginit) {
        s.push('\0');
        let temp = self.gensym(&format!("{name}_tmp"));
        let array_ty = llast::Ty::Array(s.len() as i64, Box::new(llast::Ty::I8));
        self.llprog.gdecls.push((temp.clone(), (array_ty.clone(), llast::Ginit::String(s))));
        assert!(self.globals.insert(temp.clone(), (temp.clone(), array_ty.clone())).is_none());

        let string_ty = llast::Ty::Ptr(Box::new(llast::Ty::I8));
        let bitcast = llast::Ginit::Bitcast(llast::Ty::Ptr(Box::new(array_ty)), Box::new(llast::Ginit::Gid(temp)), string_ty.clone());
        (string_ty, bitcast)
    }

    fn add_function_to_globals(&mut self, func: &oast::Fdecl) {
        let ret_ty = tipe(func.ret_ty.clone());
        let (arg_tys, _): (Vec<_>, Vec<_>) = func.args.iter().cloned().map(|(t, n)| (tipe(t), n)).unzip();
        let fun_ty = llast::FunTy {
            params: arg_tys,
            ret: ret_ty,
        };

        let ty_fun = llast::Ty::Fun(fun_ty.params.clone(), Box::new(fun_ty.ret.clone()));
        assert!(self.globals.insert(func.name.clone(), (func.name.clone(), ty_fun)).is_none());

    }

    fn function(&mut self, func: oast::Fdecl) {
        let ret_ty = tipe(func.ret_ty);
        let (arg_tys, names): (Vec<_>, Vec<_>) = func.args.into_iter().map(|(t, n)| (tipe(t), n)).unzip();
        let fun_ty = llast::FunTy {
            params: arg_tys,
            ret: ret_ty,
        };

        let post_entry_lbl = "post_entry".to_string();

        let mut fun_ctx = FunContext {
            cfg: llast::Cfg {
                entry: llast::Block {
                    insns: Default::default(),
                    term: (self.gensym("_"), llast::Terminator::Br(post_entry_lbl.clone())),
                },
                blocks: vec![],
            },
            locals: Default::default(),
            ret_ty: fun_ty.ret.clone(),
            current: Default::default(),
        };

        fun_ctx.push_scope();

        for (n, ty) in names.iter().zip(fun_ty.params.iter()) {
            let uid = self.gensym(n);
            fun_ctx.cfg.entry.insns.push((uid.clone(), llast::Insn::Alloca(ty.clone())));
            fun_ctx.add_local(n.clone(), (uid.clone(), ty.clone()));
            fun_ctx.cfg.entry.insns.push((self.gensym("_"), llast::Insn::Store(ty.clone(), llast::Operand::Id(n.clone()), llast::Operand::Id(uid.clone()))));
        }

        fun_ctx.start_block(post_entry_lbl);

        self.block(&mut fun_ctx, func.body);
        fun_ctx.pop_scope();
        assert_eq!(fun_ctx.locals.len(), 0);

        // todo: temp fix
        fun_ctx.cfg.blocks.retain(|(lbl, _)| !lbl.starts_with("__unreachable"));

        /*
        crappy codegen prevents me from doing this
        assert_eq!(fun_ctx.current.0, None);
        assert_eq!(fun_ctx.current.1, vec![]);
        assert_eq!(fun_ctx.current.2, None);
        */

        let fdecl = llast::Fdecl {
            ty: fun_ty,
            params: names,
            cfg: fun_ctx.cfg,
        };

        self.llprog.fdecls.push((func.name, fdecl));
    }

    fn block(&mut self, fun_ctx: &mut FunContext, body: oast::Block) {
        for stmt in body {
            self.stmt(fun_ctx, stmt.t);
        }
    }

    fn stmt(&mut self, fun_ctx: &mut FunContext, stmt: oast::Stmt) {
        match stmt {
            oast::Stmt::Assn(lhs, rhs) => {
                // todo: evaluation order?
                let (rhs_op, ty) = self.exp(fun_ctx, rhs.t);
                let (lhs_ptr_op, pointee_ty) = self.lhs(fun_ctx, lhs.t);
                debug_assert_eq!(ty, pointee_ty);
                fun_ctx.push_insn(self.gensym("_"), llast::Insn::Store(ty.clone(), rhs_op, lhs_ptr_op));
            },
            oast::Stmt::Decl(d) => {
                self.vdecl(fun_ctx, d);
            },
            oast::Stmt::Ret(v) => {
                let ret_op = v.map(|v| self.exp(fun_ctx, v.t).0);
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Ret(fun_ctx.ret_ty.clone(), ret_op));
                // todo: bad codegen :(
                fun_ctx.start_block(self.gensym("_unreachable"));
            },
            oast::Stmt::Call(f, args) => {
                let uid = self.gensym("_");
                self.call(fun_ctx, f.t, args, uid);
            }
            oast::Stmt::If(cnd, if_blk, else_blk) => {
                let (cnd_op, _ty) = self.exp(fun_ctx, cnd.t);
                let then_lbl = self.gensym("then");
                let else_lbl = self.gensym("else");
                let after_lbl = self.gensym("after");
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Cbr(cnd_op, then_lbl.clone(), else_lbl.clone()));

                fun_ctx.push_scope();
                fun_ctx.start_block(then_lbl.clone());
                self.block(fun_ctx, if_blk);
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(after_lbl.clone()));
                fun_ctx.pop_scope();

                fun_ctx.push_scope();
                fun_ctx.start_block(else_lbl.clone());
                self.block(fun_ctx, else_blk);
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(after_lbl.clone()));
                fun_ctx.pop_scope();

                fun_ctx.start_block(after_lbl.clone());
            }
            oast::Stmt::IfNull(_, _, _, _, _) => todo!(),
            oast::Stmt::For(vdecls, cnd, update, blk) => {
                // todo: fix up kinda crappy code gen
                let for_top_lbl = self.gensym("for_top");
                let for_body_lbl = self.gensym("for_body");
                let for_update_lbl = self.gensym("for_update");
                let for_after_lbl = self.gensym("after_for");

                fun_ctx.push_scope();
                for vd in vdecls {
                    self.vdecl(fun_ctx, vd);
                }
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(for_top_lbl.clone()));

                fun_ctx.start_block(for_top_lbl.clone());
                let cnd_op = if let Some(cnd) = cnd {
                    let (cnd_op, _ty) = self.exp(fun_ctx, cnd.t);
                    cnd_op
                } else {
                    llast::Operand::Const(1)
                };
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Cbr(cnd_op, for_body_lbl.clone(), for_after_lbl.clone()));

                fun_ctx.start_block(for_body_lbl.clone());
                self.block(fun_ctx, blk);
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(for_update_lbl.clone()));

                fun_ctx.start_block(for_update_lbl.clone());
                if let Some(upd) = update {
                    self.stmt(fun_ctx, upd.t);
                }
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(for_top_lbl.clone()));
                fun_ctx.pop_scope();

                fun_ctx.start_block(for_after_lbl.clone());
            }
            oast::Stmt::While(cnd, blk) => {
                let while_top_lbl = self.gensym("while_top");
                let while_body_lbl = self.gensym("while_body");
                let while_after_lbl = self.gensym("while_after");
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(while_top_lbl.clone()));

                fun_ctx.start_block(while_top_lbl.clone());
                let (cnd_op, _ty) = self.exp(fun_ctx, cnd.t);
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Cbr(cnd_op, while_body_lbl.clone(), while_after_lbl.clone()));

                fun_ctx.push_scope();
                fun_ctx.start_block(while_body_lbl.clone());
                self.block(fun_ctx, blk);
                fun_ctx.terminate(self.gensym("_"), llast::Terminator::Br(while_top_lbl.clone()));
                fun_ctx.pop_scope();

                fun_ctx.start_block(while_after_lbl.clone());
            }
        }
    }

    fn vdecl(&mut self, fun_ctx: &mut FunContext, d: oast::Vdecl) {
        let (exp_uid, ty) = self.exp(fun_ctx, d.exp.t);
        let alloca = llast::Insn::Alloca(ty.clone());
        let alloca_uid = self.gensym(&d.name);
        fun_ctx.cfg.entry.insns.push((alloca_uid.clone(), alloca));
        fun_ctx.add_local(d.name.clone(), (alloca_uid.clone(), ty.clone()));
        fun_ctx.push_insn(self.gensym("_"), llast::Insn::Store(ty.clone(), exp_uid, llast::Operand::Id(alloca_uid)));
    }

    fn exp(&mut self, fun_ctx: &mut FunContext, exp: oast::Exp) -> (llast::Operand, llast::Ty) {
        let (op, ty): (llast::Operand, llast::Ty) = match exp {
            oast::Exp::Null(t) => (llast::Operand::Const(0), tipe(t)),
            oast::Exp::Bool(b) => (llast::Operand::Const(b as i64), llast::Ty::I1),
            oast::Exp::Int(n) => (llast::Operand::Const(n), llast::Ty::I64),
            oast::Exp::Str(s) => {
                let gid = self.gensym("string");
                let (ty, ginit) = self.global_string(gid.clone(), s);
                self.llprog.gdecls.push((gid.clone(), (ty.clone(), ginit)));
                assert!(self.globals.insert(gid.clone(), (gid.clone(), ty)).is_none());

                let ty = llast::Ty::Ptr(Box::new(llast::Ty::I8));
                let insn = llast::Insn::Load(ty.clone(), llast::Operand::Gid(gid));
                let uid = self.gensym("uid");
                fun_ctx.push_insn(uid.clone(), insn);
                (llast::Operand::Id(uid), ty)
            }
            oast::Exp::ArrElems(ty, els) => {
                let (array_op, array_ty, array_base_ty) = self.oat_alloc_array(fun_ctx, tipe(ty), llast::Operand::Const(els.len() as i64));

                for (ix, el) in els.into_iter().enumerate() {
                    let (op, ty) = self.exp(fun_ctx, el.t);
                    let ix_ptr_uid = self.gensym("ix");
                    let ix_ptr_insn = llast::Insn::Gep(array_base_ty.clone(), array_op.clone(), vec![llast::Operand::Const(0), llast::Operand::Const(1), llast::Operand::Const(ix as i64)]);
                    fun_ctx.push_insn(ix_ptr_uid.clone(), ix_ptr_insn);
                    fun_ctx.push_insn(self.gensym("_"), llast::Insn::Store(ty, op, llast::Operand::Id(ix_ptr_uid)));
                }

                (array_op, array_ty)
            }
            oast::Exp::ArrLen(ty, len) => {
                let (op, _) = self.exp(fun_ctx, len.t);
                let (array_op, array_ty, _) = self.oat_alloc_array(fun_ctx, tipe(ty), op);
                (array_op, array_ty)
            }
            oast::Exp::ArrInit(_, _, _, _) => todo!(),
            oast::Exp::Length(_) => todo!(),
            oast::Exp::Struct(_, _) => todo!(),
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
                        let op2 = if t1 != t2 {
                            let e2_uid = self.gensym("eq_cast");
                            fun_ctx.push_insn(e2_uid.clone(), llast::Insn::Bitcast(t2, op2, t1.clone()));
                            llast::Operand::Id(e2_uid)
                        } else {
                            op2
                        };

                        let bop = if obop == oast::Binop::Eq {
                            llast::Cnd::Eq
                        } else {
                            llast::Cnd::Ne
                        };

                        (t1.clone(), llast::Insn::Icmp(bop, t1.clone(), op1, op2))
                    }
                };
                let uid = self.gensym("bop");
                fun_ctx.push_insn(uid.clone(), insn);
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
                fun_ctx.push_insn(uid.clone(), insn);
                (llast::Operand::Id(uid), t2)
            }
            e@(oast::Exp::Id(..) | oast::Exp::Proj(..) | oast::Exp::Index(..)) => {
                let name = match &e {
                    oast::Exp::Id(id) => id.clone(),
                    oast::Exp::Proj(_, field) => field.clone(),
                    oast::Exp::Index(..) => "index".to_string(),
                    _ => unreachable!(),
                };
                let (ptr_operand, pointee_ty) = self.lhs(fun_ctx, e);
                if let llast::Ty::Fun(..) = &pointee_ty {
                    (ptr_operand, llast::Ty::Ptr(Box::new(pointee_ty)))
                } else {
                    let load_uid = self.gensym(&name);
                    let load_insn = llast::Insn::Load(pointee_ty.clone(), ptr_operand);
                    fun_ctx.push_insn(load_uid.clone(), load_insn);
                    (llast::Operand::Id(load_uid), pointee_ty.clone())
                }
            }
        };

        (op, ty)
    }

    fn oat_alloc_array(&mut self, fun_ctx: &mut FunContext, ty: llast::Ty, len: llast::Operand) -> (llast::Operand, llast::Ty, llast::Ty) {
        let (i64_ptr_op, i64_ptr_ty) = self.call_builtin(fun_ctx, "oat_alloc_array", &[len]);
        let array_uid = self.gensym("array");
        let array_base_ty = array_maker(ty, 0);
        let array_ty = ptr_maker(array_base_ty.clone());
        fun_ctx.push_insn(array_uid.clone(), llast::Insn::Bitcast(i64_ptr_ty, i64_ptr_op.clone(), array_ty.clone()));

        (llast::Operand::Id(array_uid), array_ty, array_base_ty)
    }

    fn call(&mut self, fun_ctx: &mut FunContext, f: oast::Exp, args: Vec<Node<oast::Exp>>, uid: llast::Uid) -> (llast::Operand, llast::Ty) {
        let (fop, tf) = self.exp(fun_ctx, f);
        let llast::Ty::Ptr(p) = tf else { unreachable!() };
        let llast::Ty::Fun(_, ret_ty) = *p else { unreachable!() };
        let args: Vec<_> = args.into_iter().map(|a| {
            let (op, t) = self.exp(fun_ctx, a.t);
            (t, op)
        }).collect();
        fun_ctx.push_insn(uid.clone(), llast::Insn::Call((*ret_ty).clone(), fop, args));
        (llast::Operand::Id(uid), *ret_ty)
    }

    /// will always return the storage slot
    fn lhs(&mut self, fun_ctx: &mut FunContext, lhs: oast::Exp) -> (llast::Operand, llast::Ty) {
        match lhs {
            oast::Exp::Id(id) => {
                // todo: support multiple scopes
                if let Some((ptr_uid, ty)) = fun_ctx.lookup_local(&id) {
                    (llast::Operand::Id(ptr_uid.clone()), ty.clone())
                } else if let Some((ptr_gid, ty)) = self.globals.get(&id) {
                    (llast::Operand::Gid(ptr_gid.clone()), ty.clone())
                } else {
                    unreachable!()
                }
            }
            oast::Exp::Proj(_, _) => todo!(),
            oast::Exp::Index(arr, ix) => {
                let (aop, aty) = self.exp(fun_ctx, arr.t);
                let (iop, _) = self.exp(fun_ctx, ix.t);

                let llast::Ty::Ptr(p) = &aty else { unreachable!() };
                let ptr_ty = p.clone();
                let llast::Ty::Struct(v) = &**p else { unreachable!() };
                let llast::Ty::Array(_, elem_ty) = &v[1] else { unreachable!() };
                let elem_ty: llast::Ty = *elem_ty.clone();

                let len_ptr = self.gensym("len");
                let len_ptr_insn = llast::Insn::Gep(*ptr_ty.clone(), aop.clone(), vec![llast::Operand::Const(0), llast::Operand::Const(0)]);
                fun_ctx.push_insn(len_ptr.clone(), len_ptr_insn);
                self.call_builtin(fun_ctx, "oat_assert_array_length", &[llast::Operand::Id(len_ptr), iop.clone()]);

                let gep_uid = self.gensym("index");
                let gep = llast::Insn::Gep(*ptr_ty, aop, vec![llast::Operand::Const(0), llast::Operand::Const(1), iop]);
                fun_ctx.push_insn(gep_uid.clone(), gep);
                (llast::Operand::Id(gep_uid), elem_ty)
            }
            _ => unreachable!(),
        }
    }

    fn call_builtin(&mut self, fun_ctx: &mut FunContext, name: &'static str, args: &[llast::Operand]) -> (llast::Operand, llast::Ty) {
        let ret = self.gensym("ret");
        let (_, ty) = self.llprog.edecls.iter().find(|(n, _)| n == name).expect("unknown builtin");
        let llast::Ty::Fun(arg_tys, ret_ty) = ty else { unreachable!() };
        let args: Vec<_> = args.iter().zip(arg_tys).map(|(a, t)| (t.clone(), a.clone())).collect();
        let ret_ty = (**ret_ty).clone();
        let insn = llast::Insn::Call(ret_ty.clone(), llast::Operand::Gid(name.to_string()), args.to_vec());
        fun_ctx.push_insn(ret.clone(), insn);
        (llast::Operand::Id(ret), ret_ty)
    }

    fn tipe_decl(&mut self, _t: oast::Tdecl) {
        todo!()
    }
}

fn array_maker(ty: llast::Ty, len: i64) -> llast::Ty {
    llast::Ty::Struct(vec![llast::Ty::I64, llast::Ty::Array(len, Box::new(ty))])
}

fn ptr_maker(ty: llast::Ty) -> llast::Ty {
    llast::Ty::Ptr(Box::new(ty))
}

fn tipe(ot: oast::Ty) -> llast::Ty {
    use oast::TyKind as TK;
    use llast::Ty as Lty;
    match ot.kind {
        TK::Void => Lty::Void,
        TK::Bool => Lty::I1,
        TK::Int => Lty::I64,
        TK::String => Lty::Ptr(Box::new(Lty::I8)),
        TK::Struct(_) => todo!(),
        TK::Array(t) => Lty::Ptr(Box::new(Lty::Struct(vec![Lty::I64, Lty::Array(0, Box::new(tipe(*t)))]))),
        TK::Fun(_, _) => todo!(),
    }
}
