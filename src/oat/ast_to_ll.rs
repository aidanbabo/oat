use std::collections::HashMap;

use super::ast as oast;
use crate::llvm::ast as llast;

struct FunContext {
    locals: HashMap<oast::Ident, (llast::Uid, llast::Ty)>,
    cfg: llast::Cfg,
    ret_ty: llast::Ty,
}

pub struct Context {
    llprog: llast::Prog,
    globals: HashMap<String, String>,
    sym_num: usize,
}

impl Context {
    pub fn new() -> Self {
        Context {
            llprog: llast::Prog {
                tdecls: Default::default(),
                gdecls: Default::default(),
                fdecls: Default::default(),
                edecls: Default::default(),
            },
            globals: Default::default(),
            sym_num: 0,
        }
    }

    pub fn lower(mut self, oprog: oast::Prog) -> llast::Prog {
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

    fn global(&mut self, v: oast::Gdecl) {
        todo!()
    }

    fn function(&mut self, func: oast::Fdecl) {
        let ret_ty = tipe(func.ret_ty);
        let (arg_tys, names): (Vec<_>, Vec<_>) = func.args.into_iter().map(|(t, n)| (tipe(t), n)).unzip();
        let fun_ty = llast::FunTy {
            params: arg_tys,
            ret: ret_ty,
        };

        let mut fun_ctx = FunContext {
            cfg: llast::Cfg {
                entry: empty_block(&fun_ty.ret.clone()),
                blocks: vec![],
            },
            locals: Default::default(),
            ret_ty: fun_ty.ret.clone(),
        };

        for (n, ty) in names.iter().zip(fun_ty.params.iter()) {
            let uid = self.gensym(n);
            fun_ctx.cfg.entry.insns.push((uid.clone(), llast::Insn::Alloca(ty.clone())));
            fun_ctx.locals.insert(n.clone(), (uid.clone(), ty.clone()));
            fun_ctx.cfg.entry.insns.push((self.gensym("_"), llast::Insn::Store(ty.clone(), llast::Operand::Id(n.clone()), llast::Operand::Id(uid.clone()))));
        }

        self.block(&mut fun_ctx, func.body);

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
                fun_ctx.cfg.current().insns.push((self.gensym("_"), llast::Insn::Store(ty.clone(), rhs_op, lhs_ptr_op)));
            },
            oast::Stmt::Decl(d) => {
                self.vdecl(fun_ctx, d);
            },
            oast::Stmt::Ret(v) => {
                let ret_op = v.map(|v| self.exp(fun_ctx, v.t).0);
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Ret(fun_ctx.ret_ty.clone(), ret_op));
                // todo: crappy codegen :/
                fun_ctx.cfg.blocks.push((self.gensym("_unreachable"), empty_block(&fun_ctx.ret_ty)));
            },
            oast::Stmt::Call(_, _) => todo!(),
            oast::Stmt::If(cnd, if_blk, else_blk) => {
                let (cnd_op, _ty) = self.exp(fun_ctx, cnd.t);
                let then_lbl = self.gensym("then");
                let else_lbl = self.gensym("else");
                let after_lbl = self.gensym("after");
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Cbr(cnd_op, then_lbl.clone(), else_lbl.clone()));

                fun_ctx.cfg.blocks.push((then_lbl.clone(), empty_block(&fun_ctx.ret_ty)));
                self.block(fun_ctx, if_blk);
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Br(after_lbl.clone()));

                fun_ctx.cfg.blocks.push((else_lbl.clone(), empty_block(&fun_ctx.ret_ty)));
                self.block(fun_ctx, else_blk);
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Br(after_lbl.clone()));

                fun_ctx.cfg.blocks.push((after_lbl.clone(), empty_block(&fun_ctx.ret_ty)));
            }
            oast::Stmt::IfNull(_, _, _, _, _) => todo!(),
            oast::Stmt::For(vdecls, cnd, update, blk) => {
                // todo: fix up kinda crappy code gen
                let for_top_lbl = self.gensym("for_top");
                let for_body_lbl = self.gensym("for_body");
                let for_update_lbl = self.gensym("for_update");
                let for_after_lbl = self.gensym("after_for");
                for vd in vdecls {
                    self.vdecl(fun_ctx, vd);
                }
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Br(for_top_lbl.clone()));

                fun_ctx.cfg.blocks.push((for_top_lbl.clone(), empty_block(&fun_ctx.ret_ty)));
                let cnd_op = if let Some(cnd) = cnd {
                    let (cnd_op, _ty) = self.exp(fun_ctx, cnd.t);
                    cnd_op
                } else {
                    llast::Operand::Const(1)
                };
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Cbr(cnd_op, for_body_lbl.clone(), for_after_lbl.clone()));

                fun_ctx.cfg.blocks.push((for_body_lbl.clone(), empty_block(&fun_ctx.ret_ty)));
                self.block(fun_ctx, blk);
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Br(for_update_lbl.clone()));

                fun_ctx.cfg.blocks.push((for_update_lbl.clone(), empty_block(&fun_ctx.ret_ty)));
                if let Some(upd) = update {
                    self.stmt(fun_ctx, upd.t);
                }
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Br(for_top_lbl.clone()));

                fun_ctx.cfg.blocks.push((for_after_lbl.clone(), empty_block(&fun_ctx.ret_ty)));
            }
            oast::Stmt::While(cnd, blk) => {
                let while_top_lbl = self.gensym("while_top");
                let while_body_lbl = self.gensym("while_body");
                let while_after_lbl = self.gensym("while_after");
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Br(while_top_lbl.clone()));

                fun_ctx.cfg.blocks.push((while_top_lbl.clone(), empty_block(&fun_ctx.ret_ty)));
                let (cnd_op, _ty) = self.exp(fun_ctx, cnd.t);
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Cbr(cnd_op, while_body_lbl.clone(), while_after_lbl.clone()));

                fun_ctx.cfg.blocks.push((while_body_lbl.clone(), empty_block(&fun_ctx.ret_ty)));
                self.block(fun_ctx, blk);
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Br(while_top_lbl.clone()));

                fun_ctx.cfg.blocks.push((while_after_lbl.clone(), empty_block(&fun_ctx.ret_ty)));
            }
        }
    }

    fn vdecl(&mut self, fun_ctx: &mut FunContext, d: oast::Vdecl) {
        let (exp_uid, ty) = self.exp(fun_ctx, d.exp.t);
        let alloca = llast::Insn::Alloca(ty.clone());
        let alloca_uid = self.gensym(&d.name);
        fun_ctx.cfg.entry.insns.push((alloca_uid.clone(), alloca));
        assert!(fun_ctx.locals.insert(d.name.clone(), (alloca_uid.clone(), ty.clone())).is_none(), "shadowed variable");
        fun_ctx.cfg.current().insns.push((self.gensym("_"), llast::Insn::Store(ty.clone(), exp_uid, llast::Operand::Id(alloca_uid))));
    }

    fn exp(&mut self, fun_ctx: &mut FunContext, exp: oast::Exp) -> (llast::Operand, llast::Ty) {
        let (op, ty): (llast::Operand, llast::Ty) = match exp {
            oast::Exp::Null(t) => (llast::Operand::Const(0), tipe(t)),
            oast::Exp::Bool(b) => (llast::Operand::Const(b as i64), llast::Ty::I1),
            oast::Exp::Int(n) => (llast::Operand::Const(n), llast::Ty::I64),
            oast::Exp::Str(_) => todo!(),
            oast::Exp::ArrElems(_, _) => todo!(),
            oast::Exp::ArrLen(_, _) => todo!(),
            oast::Exp::ArrInit(_, _, _, _) => todo!(),
            oast::Exp::Length(_) => todo!(),
            oast::Exp::Struct(_, _) => todo!(),
            oast::Exp::Call(_, _) => todo!(),
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
                            fun_ctx.cfg.current().insns.push((e2_uid.clone(), llast::Insn::Bitcast(t2, op2, t1.clone())));
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
                let uid = self.gensym("tmp");
                fun_ctx.cfg.current().insns.push((uid.clone(), insn));
                (llast::Operand::Id(uid), t3)
            },
            oast::Exp::Uop(ouop, exp) => {
                let (e1, _t1) = self.exp(fun_ctx, exp.t);
                let (t2, insn) = match ouop {
                    oast::Unop::Neg => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::Sub, llast::Ty::I64, llast::Operand::Const(0), e1)),
                    oast::Unop::LogNot => (llast::Ty::I1, llast::Insn::Icmp(llast::Cnd::Eq, llast::Ty::I1, llast::Operand::Const(0), e1)),
                    oast::Unop::BitNot => (llast::Ty::I64, llast::Insn::Binop(llast::Bop::Xor, llast::Ty::I64, llast::Operand::Const(-1), e1)),
                };
                let uid = self.gensym("tmp");
                fun_ctx.cfg.current().insns.push((uid.clone(), insn));
                (llast::Operand::Id(uid), t2)
            }
            oast::Exp::Id(..) | oast::Exp::Proj(..) | oast::Exp::Index(..) => {
                let (ptr_operand, pointee_ty) = self.lhs(fun_ctx, exp);
                let load_insn = llast::Insn::Load(pointee_ty.clone(), ptr_operand);
                let load_uid = self.gensym("tmp"); // todo: better name?
                fun_ctx.cfg.current().insns.push((load_uid.clone(), load_insn));
                (llast::Operand::Id(load_uid), pointee_ty.clone())
            }
        };

        (op, ty)
    }

    /// will always return the storage slot
    fn lhs(&mut self, fun_ctx: &mut FunContext, lhs: oast::Exp) -> (llast::Operand, llast::Ty) {
        match lhs {
            oast::Exp::Id(id) => {
                // todo: support globals
                // todo: support multiple scopes
                let (ptr_uid, ty) = fun_ctx.locals.get(&id).expect("can't find local variable");
                (llast::Operand::Id(ptr_uid.clone()), ty.clone())
            },
            oast::Exp::Proj(_, _) => todo!(),
            oast::Exp::Index(_, _) => todo!(),
            _ => unreachable!(),
        }
    }

    fn tipe_decl(&mut self, t: oast::Tdecl) {
        todo!()
    }
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

fn empty_block(ret_ty: &llast::Ty) -> llast::Block {
    let ret_val = if let llast::Ty::Void = ret_ty {
        None
    } else {
        Some(llast::Operand::Const(0))
    };
    llast::Block {
        insns: vec![],
        term: ("__garbage__".to_string(), llast::Terminator::Ret(ret_ty.clone(), ret_val)),
    }
}

impl llast::Cfg {
    pub fn current(&mut self) -> &mut llast::Block {
        if let Some(last) = self.blocks.last_mut() {
            &mut last.1
        } else {
            &mut self.entry
        }
    }
}
