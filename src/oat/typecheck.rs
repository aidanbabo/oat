use std::collections::{HashMap, HashSet};

use super::ast::*;
use super::Node;

#[derive(Debug)]
pub struct TypeError(String);

fn subtype(sub: &Ty, sup: &Ty) -> bool {
    let simple_reflexive = matches!((&sub.kind, &sup.kind), (TyKind::Void, TyKind::Void) | (TyKind::Bool, TyKind::Bool) | (TyKind::Int, TyKind::Int));
    if simple_reflexive {
        return true;
    }

    if !sup.nullable && sub.nullable {
        return false;
    }

    match (&sub.kind, &sup.kind) {
        (TyKind::String, TyKind::String) => true,
        (TyKind::Array(sub), TyKind::Array(sup)) => sub == sup,
        (TyKind::Struct(_sub_n), TyKind::Struct(_sup_n)) => todo!(),
        (TyKind::Fun(sub_args, sub_ret), TyKind::Fun(sup_args, sup_ret)) if sub_args.len() == sup_args.len() => {
            subtype(sub_ret, sup_ret) && 
                sub_args
                .iter()
                .zip(sup_args.iter())
                .all(|(sub, sup)| subtype(sup, sub))
        }
        _ => false
    }
}

fn bop_ty(b: Binop) -> (Ty, Ty, Ty) {
    let int_ty = Ty { nullable: false, kind: TyKind::Int };
    let bool_ty = Ty { nullable: false, kind: TyKind::Bool };
    match b {
        Binop::Add | Binop::Sub | Binop::Mul | Binop::Shl | Binop::Shr | Binop::Sar | Binop::IAnd | Binop::IOr => (int_ty.clone(), int_ty.clone(), int_ty),
        Binop::Lt | Binop::Lte | Binop::Gt | Binop::Gte => (int_ty.clone(), int_ty, bool_ty),
        Binop::And | Binop::Or => (bool_ty.clone(), bool_ty.clone(), bool_ty),
        Binop::Eq | Binop::Neq => unreachable!(),
    }
}

fn uop_ty(u: Unop) -> (Ty, Ty) {
    let int_ty = Ty { nullable: false, kind: TyKind::Int };
    let bool_ty = Ty { nullable: false, kind: TyKind::Bool };
    match u {
        Unop::Neg | Unop::BitNot => (int_ty.clone(), int_ty),
        Unop::LogNot => (bool_ty.clone(), bool_ty),
    }
}

fn gexp(e: &Exp, globals: &HashMap<Ident, Ty>) -> Result<Ty, TypeError> {
    let ty = match e {
        Exp::Null(t) => Ty { nullable: true, kind: t.kind.clone() },
        Exp::Bool(_) => Ty { nullable: false, kind: TyKind::Bool },
        Exp::Int(_) => Ty { nullable: false, kind: TyKind::Int },
        Exp::Str(_) => Ty { nullable: false, kind: TyKind::String },
        Exp::Id(name) => globals.get(name).expect("no such variable").clone(),
        Exp::ArrElems(t, els) => {
            for e in els {
                let sub = gexp(e, globals)?;
                if !subtype(&sub, t) {
                    return Err(TypeError("array elem isn't a subtype".to_string()));
                }
            }
            Ty { nullable: false, kind: TyKind::Array(Box::new(t.clone())) }
        },
        _ => unreachable!(),
    };

    Ok(ty)
}

fn call(f: &Exp, args: &[Node<Exp>], locals: &HashMap<Ident, Ty>, globals: &HashMap<Ident, Ty>) -> Result<Ty, TypeError> {
    let f_ty = exp(f, locals, globals)?;
    if f_ty.nullable {
        return Err(TypeError("can't call a possibly null value".to_string()));
    }

    let TyKind::Fun(arg_tys, ret_ty) = f_ty.kind else {
        return Err(TypeError("can't call a non-function type".to_string()));
    };

    if args.len() != arg_tys.len() {
        return Err(TypeError("wrong number of function arguments".to_string()));
    }

    for (arg, expected_ty) in args.iter().zip(arg_tys.iter()) {
        let actual_ty = exp(arg, locals, globals)?;
        if !subtype(&actual_ty, expected_ty) {
            return Err(TypeError(format!("can't pass {actual_ty:?} to a function expecting {expected_ty:?}")));
        }
    }

    Ok(*ret_ty)
}

fn exp(e: &Exp, locals: &HashMap<Ident, Ty>, globals: &HashMap<Ident, Ty>) -> Result<Ty, TypeError> {
    let ty = match e {
        Exp::Null(t) => Ty { nullable: true, kind: t.kind.clone() },
        Exp::Bool(_) => Ty { nullable: false, kind: TyKind::Bool },
        Exp::Int(_) => Ty { nullable: false, kind: TyKind::Int },
        Exp::Str(_) => Ty { nullable: false, kind: TyKind::String },
        Exp::Id(n) => {
            if let Some(ty) = locals.get(n) {
                ty.clone()
            } else if let Some(ty) = globals.get(n) {
                ty.clone()
            } else {
                return Err(TypeError(format!("no such binding {n}")));
            }
        }
        Exp::ArrElems(t, els) => {
            for e in els {
                let sub = exp(e, locals, globals)?;
                if !subtype(&sub, t) {
                    return Err(TypeError("array elem isn't a subtype".to_string()));
                }
            }
            Ty { nullable: false, kind: TyKind::Array(Box::new(t.clone())) }
        }
        Exp::ArrLen(ty, len) => {
            if ty.kind.is_ref() && !ty.nullable {
                return Err(TypeError("cannot have non-nullable reference types in default initialized arrays".to_string()));
            }
            if exp(len, locals, globals)? != (Ty { nullable: false, kind: TyKind::Int }) {
                return Err(TypeError("len must be an int".to_string()));
            }
            Ty { nullable: false, kind: TyKind::Array(Box::new(ty.clone())) }
        }
        Exp::ArrInit(_, _, _, _) => todo!(),
        Exp::Index(arr, ix) => {
            let a_ty = exp(arr, locals, globals)?;
            let ix_ty = exp(ix, locals, globals)?;

            if a_ty.nullable {
                return Err(TypeError("cannot index into possibly null type. consider using a cast (if?) first".to_string()));
            }

            let TyKind::Array(t) = a_ty.kind else {
                return Err(TypeError("cannot index into non-array type".to_string()));
            };

            if ix_ty != (Ty { nullable: false, kind: TyKind::Int }) {
                return Err(TypeError("array index must be an int".to_string()));
            }

            (*t).clone()
        }
        Exp::Length(_) => todo!(),
        Exp::Struct(_, _) => todo!(),
        Exp::Proj(_, _) => todo!(),
        Exp::Call(f, args) => call(f, args, locals, globals)?,
        Exp::Bop(Binop::Eq | Binop::Neq, lhs, rhs) => {
            let l_ty = exp(lhs, locals, globals)?;
            let r_ty = exp(rhs, locals, globals)?;
            if subtype(&l_ty, &r_ty) && subtype(&r_ty, &l_ty) {
                Ty { nullable: false, kind: TyKind::Bool }
            } else {
                return Err(TypeError("lhs and rhs to == or != must be of the same type".to_string()));
            }
        }
        Exp::Bop(b, lhs, rhs) => {
            let l_ty = exp(lhs, locals, globals)?;
            let r_ty = exp(rhs, locals, globals)?;
            let b_ty = bop_ty(*b);
            if l_ty == b_ty.0 && r_ty == b_ty.1 {
                b_ty.2
            } else {
                return Err(TypeError("incorrect types for binary operator".to_string()));
            }
        }
        Exp::Uop(u, e) => {
            let ty = exp(e, locals, globals)?;
            let u_ty = uop_ty(*u);
            if ty == u_ty.0 {
                u_ty.1
            } else {
                return Err(TypeError("incorrect types for unary operator".to_string()));
            }
        }
    };
    Ok(ty)
}

fn vdecl(vd: &Vdecl, locals: &mut HashMap<Ident, Ty>, globals: &HashMap<Ident, Ty>) -> Result<(), TypeError> {
    let ty = exp(&vd.exp, locals, globals)?;
    if let Some(_existing_binding) = locals.insert(vd.name.clone(), ty) {
        // todo: not really a type error now is it
        return Err(TypeError("there is already a binding for this variable".to_string()));
    }

    Ok(())
}

fn stmt(s: &Stmt, ret_ty: &Ty, locals: &mut HashMap<Ident, Ty>, globals: &HashMap<Ident, Ty>) -> Result<(), TypeError> {
    match s {
        Stmt::Assn(lhs, rhs) => {
            let l_ty = exp(lhs, locals, globals)?;
            let r_ty = exp(rhs, locals, globals)?;
            if !subtype(&r_ty, &l_ty) {
                return Err(TypeError("rhs must be a subtype of the lhs".to_string()));
            }
        }
        Stmt::Decl(vd) => vdecl(vd, locals, globals)?,
        Stmt::Ret(val) => {
            let ty = if let Some(val) = val {
                exp(val, locals, globals)?
            } else {
                Ty { nullable: false, kind: TyKind::Void }
            };

            if !subtype(&ty, ret_ty) {
                return Err(TypeError("return value must match function return type".to_string()));
            }
        }
        Stmt::Call(f, args) => {
            let ty = call(f, args, locals, globals)?;
            if ty != (Ty { nullable: false, kind: TyKind::Void }) {
                return Err(TypeError("expected void return for function call statement".to_string()));
            }
        }
        Stmt::If(cnd, if_blk, else_blk) => {
            let cnd_ty = exp(cnd, locals, globals)?;
            if cnd_ty != (Ty { nullable: false, kind: TyKind::Bool }) {
                return Err(TypeError("if condition must be a bool".to_string()));
            }
            block(if_blk, ret_ty, &mut locals.clone(), globals)?;
            block(else_blk, ret_ty, &mut locals.clone(), globals)?;
        }
        Stmt::IfNull(_, _, _, _, _) => todo!(),
        Stmt::For(vds, cnd, upd, blk) => {
            let mut for_locals = locals.clone();
            for vd in vds {
                vdecl(vd, &mut for_locals, globals)?;
            }

            if let Some(cnd) = cnd {
                let cnd_ty = exp(cnd, &for_locals, globals)?;
                if cnd_ty != (Ty { nullable: false, kind: TyKind::Bool }) {
                    return Err(TypeError("while condition must be a bool".to_string()));
                }
            }

            if let Some(upd) = upd {
                stmt(upd, ret_ty, &mut for_locals.clone(), globals)?;
            }

            block(blk, ret_ty, &mut for_locals.clone(), globals)?;
        }
        Stmt::While(cnd, blk) => {
            let cnd_ty = exp(cnd, locals, globals)?;
            if cnd_ty != (Ty { nullable: false, kind: TyKind::Bool }) {
                return Err(TypeError("while condition must be a bool".to_string()));
            }
            block(blk, ret_ty, &mut locals.clone(), globals)?;
        }
    }
    Ok(())
}

fn block(b: &Block, ret_ty: &Ty, locals: &mut HashMap<Ident, Ty>, globals: &HashMap<Ident, Ty>) -> Result<(), TypeError> {
    for s in b {
        stmt(s, ret_ty, locals, globals)?;
    }
    Ok(())
}

fn function_body(f: &Fdecl, globals: &HashMap<Ident, Ty>) -> Result<(), TypeError> {
    let mut locals: HashMap<Ident, Ty> = f.args.iter().map(|(t, n)| (n.clone(), t.clone())).collect();

    block(&f.body, &f.ret_ty, &mut locals, globals)?;

    // todo: ends in return

    Ok(())
}

fn global(g: &Gdecl, globals: &HashMap<Ident, Ty>) -> Result<(Ident, Ty), TypeError> {
    Ok((g.name.clone(), gexp(&g.init, globals)?))
}

fn function_header(f: &Fdecl) -> Result<(Ident, Ty), TypeError> {
    // todo: not really a type error
    let set: HashSet<_> = f.args.iter().map(|(_, n)| n).collect();
    if set.len() != f.args.len() {
        return Err(TypeError("cannot have two function parameters with the same name".to_string()));
    }

    let ty = Ty { nullable: false, kind: TyKind::Fun(f.args.iter().map(|(t, _)| t).cloned().collect(), Box::new(f.ret_ty.clone())) };
    Ok((f.name.clone(), ty))
}

pub fn check(prog: &Prog) -> Result<(), TypeError> {
    // todo: check for duplicates
    let mut globals: HashMap<Ident, Ty> = Default::default();

    // todo: struct types

    for decl in prog {
        if let Decl::Fun(f) = decl {
            let (name, ty) = function_header(f)?;
            globals.insert(name, ty);
        }
    }

    for decl in prog {
        if let Decl::Var(v) = decl {
            let (name, ty) = global(v, &globals)?;
            globals.insert(name, ty);
        }
    }

    for decl in prog {
        // todo: struct members
        if let Decl::Fun(f) = decl {
            function_body(f, &globals)?;
        }
    }

    Ok(())
}

