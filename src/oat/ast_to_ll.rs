use std::collections::HashMap;

use super::ast as oast;
use crate::llvm::ast as llast;

struct FunContext {
    locals: HashMap<String, String>,
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
                entry: empty_block(),
                blocks: vec![],
            },
            locals: Default::default(),
            ret_ty: fun_ty.ret.clone(),
        };

        for (n, ty) in names.iter().zip(fun_ty.params.iter()) {
            let uid = self.gensym(n);
            fun_ctx.cfg.entry.insns.push((uid.clone(), llast::Insn::Alloca(ty.clone())));
            fun_ctx.locals.insert(n.clone(), uid.clone());
            fun_ctx.cfg.entry.insns.push((self.gensym("_"), llast::Insn::Store(ty.clone(), llast::Operand::Id(n.clone()), llast::Operand::Id(uid.clone()))));
        }

        self.cfg(&mut fun_ctx, func.body);

        let fdecl = llast::Fdecl {
            ty: fun_ty,
            params: names,
            cfg: fun_ctx.cfg,
        };

        self.llprog.fdecls.push((func.name, fdecl));
    }

    fn cfg(&mut self, fun_ctx: &mut FunContext, body: oast::Block) {
        for stmt in body {
            self.stmt(fun_ctx, stmt.t);
        }
    }

    fn stmt(&mut self, fun_ctx: &mut FunContext, stmt: oast::Stmt) {
        match stmt {
            oast::Stmt::Assn(_, _) => todo!(),
            oast::Stmt::Decl(_) => todo!(),
            oast::Stmt::Ret(v) => {
                let ret_uid = v.map(|v| self.exp(fun_ctx, v.t));
                fun_ctx.cfg.current().term = (self.gensym("_"), llast::Terminator::Ret(fun_ctx.ret_ty.clone(), ret_uid));
            },
            oast::Stmt::Call(_, _) => todo!(),
            oast::Stmt::If(_, _, _) => todo!(),
            oast::Stmt::IfNull(_, _, _, _, _) => todo!(),
            oast::Stmt::For(_, _, _, _) => todo!(),
            oast::Stmt::While(_, _) => todo!(),
        }
    }

    fn exp(&mut self, fun_ctx: &mut FunContext, exp: oast::Exp) -> llast::Operand {
        match exp {
            oast::Exp::Null(_) => todo!(),
            oast::Exp::Bool(_) => todo!(),
            oast::Exp::Int(n) => llast::Operand::Const(n),
            oast::Exp::Str(_) => todo!(),
            oast::Exp::Id(_) => todo!(),
            oast::Exp::ArrElems(_, _) => todo!(),
            oast::Exp::ArrLen(_, _) => todo!(),
            oast::Exp::ArrInit(_, _, _, _) => todo!(),
            oast::Exp::Index(_, _) => todo!(),
            oast::Exp::Length(_) => todo!(),
            oast::Exp::Struct(_, _) => todo!(),
            oast::Exp::Proj(_, _) => todo!(),
            oast::Exp::Call(_, _) => todo!(),
            oast::Exp::Bop(obop, lhs, rhs) => {
                let e1 = self.exp(fun_ctx, lhs.t);
                let e2 = self.exp(fun_ctx, rhs.t);
                let insn = match obop {
                    oast::Binop::Add => llast::Insn::Binop(llast::Bop::Add, llast::Ty::I64, e1, e2),
                    oast::Binop::Sub => llast::Insn::Binop(llast::Bop::Sub, llast::Ty::I64, e1, e2),
                    oast::Binop::Mul => llast::Insn::Binop(llast::Bop::Mul, llast::Ty::I64, e1, e2),
                    oast::Binop::Eq => todo!(),
                    oast::Binop::Neq => todo!(),
                    oast::Binop::Lt => llast::Insn::Icmp(llast::Cnd::Eq, llast::Ty::I64, e1, e2),
                    oast::Binop::Lte => llast::Insn::Icmp(llast::Cnd::Eq, llast::Ty::I64, e1, e2),
                    oast::Binop::Gt => llast::Insn::Icmp(llast::Cnd::Eq, llast::Ty::I64, e1, e2),
                    oast::Binop::Gte => llast::Insn::Icmp(llast::Cnd::Eq, llast::Ty::I64, e1, e2),
                    oast::Binop::And => llast::Insn::Icmp(llast::Cnd::Eq, llast::Ty::I1, e1, e2),
                    oast::Binop::Or => llast::Insn::Icmp(llast::Cnd::Eq, llast::Ty::I1, e1, e2),
                    oast::Binop::IAnd => llast::Insn::Binop(llast::Bop::And, llast::Ty::I64, e1, e2),
                    oast::Binop::IOr => llast::Insn::Binop(llast::Bop::Or, llast::Ty::I64, e1, e2),
                    oast::Binop::Shl => llast::Insn::Binop(llast::Bop::Shl, llast::Ty::I64, e1, e2),
                    oast::Binop::Shr => llast::Insn::Binop(llast::Bop::Lshr, llast::Ty::I64, e1, e2),
                    oast::Binop::Sar => llast::Insn::Binop(llast::Bop::Ashr, llast::Ty::I64, e1, e2),
                };
                let uid = self.gensym("tmp");
                fun_ctx.cfg.current().insns.push((uid.clone(), insn));
                llast::Operand::Id(uid)
            },
            oast::Exp::Uop(_, _) => todo!(),
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

fn empty_block() -> llast::Block {
    llast::Block {
        insns: vec![],
        term: ("<garbage>".to_string(), llast::Terminator::Br("<garbage>".to_string())),
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
