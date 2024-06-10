use once_cell::sync::Lazy;
use internment::Arena;

use std::collections::{HashMap, HashSet};

use super::ast::*;
use super::Node;

#[derive(Debug)]
pub struct TypeError(pub String);

pub struct Context<'ast> {
    pub structs: HashMap<Ident<'ast>, Vec<(Ty<'ast>, Ident<'ast>)>>,
    pub vars: HashMap<Ident<'ast>, Ty<'ast>>,
    pub funcs: HashMap<Ident<'ast>, Ty<'ast>>,
}

pub static BUILTINS: Lazy<HashMap<&str, Ty>> = Lazy::new(|| {
    let string_type = Ty { nullable: false, kind: TyKind::String };
    let int_array_type = Ty { nullable: false, kind: TyKind::Array(Box::new(Ty { nullable: false, kind: TyKind::Int })) };
    let void_ty = Ty { nullable: false, kind: TyKind::Void };
    let int_ty = Ty { nullable: false, kind: TyKind::Int };
    let bool_ty = Ty { nullable: false, kind: TyKind::Bool };

    let mut builtins = HashMap::new();
    builtins.insert("print_string", Ty { nullable: false, kind: TyKind::Fun(vec![string_type.clone()], Box::new(void_ty.clone()))});
    builtins.insert("print_int", Ty { nullable: false, kind: TyKind::Fun(vec![int_ty.clone()], Box::new(void_ty.clone()))});
    builtins.insert("print_bool", Ty { nullable: false, kind: TyKind::Fun(vec![bool_ty.clone()], Box::new(void_ty))});
    builtins.insert("array_of_string", Ty { nullable: false, kind: TyKind::Fun(vec![string_type.clone()], Box::new(int_array_type.clone()))});
    builtins.insert("string_of_array", Ty { nullable: false, kind: TyKind::Fun(vec![int_array_type], Box::new(string_type.clone()))});
    builtins.insert("string_of_int", Ty { nullable: false, kind: TyKind::Fun(vec![int_ty.clone()], Box::new(string_type.clone()))});
    builtins.insert("length_of_string", Ty { nullable: false, kind: TyKind::Fun(vec![string_type.clone()], Box::new(int_ty))});
    builtins.insert("string_cat", Ty { nullable: false, kind: TyKind::Fun(vec![string_type.clone(), string_type.clone()], Box::new(string_type))});
    builtins
});

fn subtype(sub: &Ty, sup: &Ty, ctx: &Context) -> bool {
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
        (TyKind::Fun(sub_args, sub_ret), TyKind::Fun(sup_args, sup_ret)) if sub_args.len() == sup_args.len() => {
            subtype(sub_ret, sup_ret, ctx) && 
                sub_args
                .iter()
                .zip(sup_args.iter())
                .all(|(sub, sup)| subtype(sup, sub, ctx))
        }
        (TyKind::Struct(sub_name), TyKind::Struct(sup_name)) => {
            if sub_name == sup_name {
                return true;
            }
            // todo: what to do here?
            let sub_fields = &ctx.structs[sub_name];
            let sup_fields = &ctx.structs[sup_name];
            if sub_fields.len() < sup_fields.len() {
                return false;
            }

            sub_fields.iter().take(sup_fields.len()).eq(sup_fields.iter())
        }
        _ => false
    }
}

fn bop_ty(b: Binop) -> (Ty<'static>, Ty<'static>, Ty<'static>) {
    let int_ty = Ty { nullable: false, kind: TyKind::Int };
    let bool_ty = Ty { nullable: false, kind: TyKind::Bool };
    match b {
        Binop::Add | Binop::Sub | Binop::Mul | Binop::Shl | Binop::Shr | Binop::Sar | Binop::IAnd | Binop::IOr => (int_ty.clone(), int_ty.clone(), int_ty),
        Binop::Lt | Binop::Lte | Binop::Gt | Binop::Gte => (int_ty.clone(), int_ty, bool_ty),
        Binop::And | Binop::Or => (bool_ty.clone(), bool_ty.clone(), bool_ty),
        Binop::Eq | Binop::Neq => unreachable!(),
    }
}

fn uop_ty(u: Unop) -> (Ty<'static>, Ty<'static>) {
    let int_ty = Ty { nullable: false, kind: TyKind::Int };
    let bool_ty = Ty { nullable: false, kind: TyKind::Bool };
    match u {
        Unop::Neg | Unop::BitNot => (int_ty.clone(), int_ty),
        Unop::LogNot => (bool_ty.clone(), bool_ty),
    }
}

fn gexp<'ast>(e: &Exp<'ast>, ctx: &Context<'ast>) -> Result<Ty<'ast>, TypeError> {
    let ty = match e {
        Exp::Null(t) => Ty { nullable: true, kind: t.kind.clone() },
        Exp::Bool(_) => Ty { nullable: false, kind: TyKind::Bool },
        Exp::Int(_) => Ty { nullable: false, kind: TyKind::Int },
        Exp::Str(_) => Ty { nullable: false, kind: TyKind::String },
        Exp::Id(name) => {
            if let Some(ty) = ctx.vars.get(name) {
                ty.clone()
            } else if let Some(ty) = ctx.funcs.get(name) {
                ty.clone()
            } else {
                return Err(TypeError(format!("unresolved global identifier {name}")));
            }
        }
        Exp::ArrElems(t, els) => {
            for e in els {
                let sub = gexp(e, ctx)?;
                if !subtype(&sub, t, ctx) {
                    return Err(TypeError("array elem isn't a subtype".to_string()));
                }
            }
            Ty { nullable: false, kind: TyKind::Array(Box::new(t.clone())) }
        },
        Exp::Struct(name, inits) => {
            let fields = ctx.structs.get(name).ok_or_else(|| TypeError(format!("unknown struct {name}")))?;
            if fields.len() != inits.len() {
                return Err(TypeError("wrong number of struct fields in struct initializer".to_string()));
            }

            for (expected_ty, name) in fields {
                let (_, e) = inits.iter().find(|(n, _)| name == n).expect("missing field member");
                let actual_ty = gexp(e, ctx)?;

                if !subtype(&actual_ty, expected_ty, ctx) {
                    return Err(TypeError(format!("wrong type in struct initializer. expected {expected_ty:?} but found {actual_ty:?}")));
                }
            }

            Ty { nullable: false, kind: TyKind::Struct(*name) }

        }
        _ => unreachable!(),
    };

    Ok(ty)
}

fn call<'ast>(f: &Exp<'ast>, args: &[Node<Exp<'ast>>], locals: &HashMap<Ident<'ast>, Ty<'ast>>, ctx: &Context<'ast>) -> Result<Ty<'ast>, TypeError> {
    let f_ty = exp(f, locals, ctx, false)?;
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
        let actual_ty = exp(arg, locals, ctx, false)?;
        if !subtype(&actual_ty, expected_ty, ctx) {
            return Err(TypeError(format!("can't pass {actual_ty:?} to a function expecting {expected_ty:?}")));
        }
    }

    Ok(*ret_ty)
}

fn exp<'ast>(e: &Exp<'ast>, locals: &HashMap<Ident<'ast>, Ty<'ast>>, ctx: &Context<'ast>, lhs: bool) -> Result<Ty<'ast>, TypeError> {
    let ty = match e {
        Exp::Null(t) => Ty { nullable: true, kind: t.kind.clone() },
        Exp::Bool(_) => Ty { nullable: false, kind: TyKind::Bool },
        Exp::Int(_) => Ty { nullable: false, kind: TyKind::Int },
        Exp::Str(_) => Ty { nullable: false, kind: TyKind::String },
        Exp::Id(n) => {
            if let Some(ty) = locals.get(n) {
                ty.clone()
            } else if let Some(ty) = ctx.vars.get(n) {
                ty.clone()
            } else if let Some(ty) = ctx.funcs.get(n) {
                if lhs {
                    return Err(TypeError("cannot use a function name as a global variable".to_string()));
                }
                ty.clone()
            } else {
                return Err(TypeError(format!("no such binding {n}")));
            }
        }
        Exp::ArrElems(t, els) => {
            for e in els {
                let sub = exp(e, locals, ctx, false)?;
                if !subtype(&sub, t, ctx) {
                    return Err(TypeError("array elem isn't a subtype".to_string()));
                }
            }
            Ty { nullable: false, kind: TyKind::Array(Box::new(t.clone())) }
        }
        Exp::ArrLen(ty, len) => {
            if ty.kind.is_ref() && !ty.nullable {
                return Err(TypeError("cannot have non-nullable reference types in default initialized arrays".to_string()));
            }
            if exp(len, locals, ctx, false)? != (Ty { nullable: false, kind: TyKind::Int }) {
                return Err(TypeError("len must be an int".to_string()));
            }
            Ty { nullable: false, kind: TyKind::Array(Box::new(ty.clone())) }
        }
        Exp::ArrInit(ty, len, name, init) => {
            let len_ty = exp(len, locals, ctx, false)?;
            let int_ty = Ty { nullable: false, kind: TyKind::Int };
            if len_ty != int_ty {
                return Err(TypeError("array length must be an int".to_string()));
            }
            let mut init_locals = locals.clone();
            if let Some(_existing_binding) = init_locals.insert(*name, int_ty) {
                // todo: not really a type error now is it
                return Err(TypeError("there is already a binding for this variable".to_string()));
            }
            let init_ty = exp(init, &init_locals, ctx, false)?;
            if !subtype(&init_ty, ty, ctx) {
                return Err(TypeError("array initializer must return subtype of the array element type".to_string()));
            }

            Ty { nullable: false, kind: TyKind::Array(Box::new(ty.clone())) }
        }
        Exp::Index(arr, ix) => {
            let a_ty = exp(arr, locals, ctx, false)?;
            let ix_ty = exp(ix, locals, ctx, false)?;

            let TyKind::Array(t) = a_ty.kind else {
                return Err(TypeError("cannot index into non-array type".to_string()));
            };

            if a_ty.nullable {
                return Err(TypeError("cannot index into possibly null array. consider using a cast (if?) first".to_string()));
            }

            if ix_ty != (Ty { nullable: false, kind: TyKind::Int }) {
                return Err(TypeError("array index must be an int".to_string()));
            }

            (*t).clone()
        }
        Exp::Length(a) => {
            let ty = exp(a, locals, ctx, false)?;
            let TyKind::Array(_) = ty.kind else {
                return Err(TypeError("cannot get length of non-array type".to_string()));
            };
            if ty.nullable {
                return Err(TypeError("cannot get length of possibly null array. consider using a cast (if?) first".to_string()));
            }
            Ty { nullable: false, kind: TyKind::Int }
        }
        Exp::Struct(name, inits) => {
            let fields = ctx.structs.get(name).ok_or_else(|| TypeError(format!("unknown struct {name}")))?;
            if fields.len() != inits.len() {
                return Err(TypeError("wrong number of struct fields in struct initializer".to_string()));
            }

            for (expected_ty, name) in fields {
                let (_, e) = inits.iter().find(|(n, _)| name == n).expect("missing field member");
                let actual_ty = exp(e, locals, ctx, false)?;

                if !subtype(&actual_ty, expected_ty, ctx) {
                    return Err(TypeError(format!("wrong type in struct initializer. expected {expected_ty:?} but found {actual_ty:?}")));
                }
            }

            Ty { nullable: false, kind: TyKind::Struct(*name) }
        }
        Exp::Proj(e, field_name) => {
            let lhs_ty = exp(e, locals, ctx, false)?;
            let TyKind::Struct(name) = lhs_ty.kind else {
                return Err(TypeError("cannot get field of non-struct type".to_string()));
            };
            if lhs_ty.nullable {
                return Err(TypeError("cannot get field of possibly null struct. consider using a cast (if?) first".to_string()));
            }
            let fields = &ctx.structs[&name];
            let Some((field_ty, _)) = fields.iter().find(|(_, n)| n == field_name) else {
                return Err(TypeError(format!("unknown field name {field_name}")));
            };
            field_ty.clone()
        }
        Exp::Call(f, args) => call(f, args, locals, ctx)?,
        Exp::Bop(Binop::Eq | Binop::Neq, lhs, rhs) => {
            let l_ty = exp(lhs, locals, ctx, false)?;
            let r_ty = exp(rhs, locals, ctx, false)?;
            if subtype(&l_ty, &r_ty, ctx) && subtype(&r_ty, &l_ty, ctx) {
                Ty { nullable: false, kind: TyKind::Bool }
            } else {
                return Err(TypeError("lhs and rhs to == or != must be of the same type".to_string()));
            }
        }
        Exp::Bop(b, lhs, rhs) => {
            let l_ty = exp(lhs, locals, ctx, false)?;
            let r_ty = exp(rhs, locals, ctx, false)?;
            let b_ty = bop_ty(*b);
            if l_ty == b_ty.0 && r_ty == b_ty.1 {
                b_ty.2
            } else {
                return Err(TypeError("incorrect types for binary operator".to_string()));
            }
        }
        Exp::Uop(u, e) => {
            let ty = exp(e, locals, ctx, false)?;
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

fn vdecl<'ast>(vd: &Vdecl<'ast>, locals: &mut HashMap<Ident<'ast>, Ty<'ast>>, ctx: &Context<'ast>) -> Result<(), TypeError> {
    let ty = exp(&vd.exp, locals, ctx, false)?;
    if ty == (Ty { nullable: false, kind: TyKind::Void }) {
        return Err(TypeError("cannot declare variable of void type".to_string()));
    }
    if let Some(_existing_binding) = locals.insert(vd.name, ty) {
        // todo: not really a type error now is it
        return Err(TypeError("there is already a binding for this variable".to_string()));
    }

    Ok(())
}

fn stmt<'ast>(s: &Stmt<'ast>, ret_ty: &Ty<'ast>, locals: &mut HashMap<Ident<'ast>, Ty<'ast>>, ctx: &Context<'ast>) -> Result<bool, TypeError> {
    match s {
        Stmt::Assn(lhs, rhs) => {
            let l_ty = exp(lhs, locals, ctx, true)?;
            let r_ty = exp(rhs, locals, ctx, false)?;
            if !subtype(&r_ty, &l_ty, ctx) {
                return Err(TypeError("rhs must be a subtype of the lhs".to_string()));
            }
            Ok(false)
        }
        Stmt::Decl(vd) => {
            vdecl(vd, locals, ctx)?;
            Ok(false)
        }
        Stmt::Ret(val) => {
            let ty = if let Some(val) = val {
                exp(val, locals, ctx, false)?
            } else {
                Ty { nullable: false, kind: TyKind::Void }
            };

            if !subtype(&ty, ret_ty, ctx) {
                return Err(TypeError("return value must match function return type".to_string()));
            }

            Ok(true)
        }
        Stmt::Call(f, args) => {
            let ty = call(f, args, locals, ctx)?;
            if ty != (Ty { nullable: false, kind: TyKind::Void }) {
                return Err(TypeError("expected void return for function call statement".to_string()));
            }
            Ok(false)
        }
        Stmt::If(cnd, if_blk, else_blk) => {
            let cnd_ty = exp(cnd, locals, ctx, false)?;
            if cnd_ty != (Ty { nullable: false, kind: TyKind::Bool }) {
                return Err(TypeError("if condition must be a bool".to_string()));
            }
            let if_returns = block(if_blk, ret_ty, &mut locals.clone(), ctx)?;
            let else_returns = block(else_blk, ret_ty, &mut locals.clone(), ctx)?;
            Ok(if_returns && else_returns)
        }
        Stmt::IfNull(ty, name, e, if_blk, else_blk) => {
            let e_ty = exp(e, locals, ctx, false)?;
            if !e_ty.nullable {
                return Err(TypeError("if? expression type must be a nullable type".to_string()));
            }
            let denulled_e_ty = Ty { nullable: false, kind: e_ty.kind };
            if !subtype(&denulled_e_ty, ty, ctx) {
                return Err(TypeError(format!("if? expression type must be a subtype of the declared type. {denulled_e_ty} needs to coerce to {ty}")));
            }

            let mut if_locals = locals.clone();
            if let Some(_existing_binding) = if_locals.insert(*name, ty.clone()) {
                // todo: not really a type error now is it
                return Err(TypeError("there is already a binding for this variable".to_string()));
            }

            let if_returns = block(if_blk, ret_ty, &mut if_locals, ctx)?;
            let else_returns = block(else_blk, ret_ty, &mut locals.clone(), ctx)?;
            Ok(if_returns && else_returns)
        }
        Stmt::For(vds, cnd, upd, blk) => {
            let mut for_locals = locals.clone();
            for vd in vds {
                vdecl(vd, &mut for_locals, ctx)?;
            }

            if let Some(cnd) = cnd {
                let cnd_ty = exp(cnd, &for_locals, ctx, false)?;
                if cnd_ty != (Ty { nullable: false, kind: TyKind::Bool }) {
                    return Err(TypeError("while condition must be a bool".to_string()));
                }
            }

            if let Some(upd) = upd {
                stmt(upd, ret_ty, &mut for_locals.clone(), ctx)?;
            }

            block(blk, ret_ty, &mut for_locals.clone(), ctx)?;
            Ok(false)
        }
        Stmt::While(cnd, blk) => {
            let cnd_ty = exp(cnd, locals, ctx, false)?;
            if cnd_ty != (Ty { nullable: false, kind: TyKind::Bool }) {
                return Err(TypeError("while condition must be a bool".to_string()));
            }
            block(blk, ret_ty, &mut locals.clone(), ctx)?;
            Ok(false)
        }
    }
}

fn block<'ast>(b: &Block<'ast>, ret_ty: &Ty<'ast>, locals: &mut HashMap<Ident<'ast>, Ty<'ast>>, ctx: &Context<'ast>) -> Result<bool, TypeError> {
    let mut returns = false;
    for s in b {
        if returns {
            return Err(TypeError("unreachable statements after statement that returns".to_string()));
        }
        if stmt(s, ret_ty, locals, ctx)? {
            returns = true;
        }
    }
    Ok(returns)
}

fn function_body<'ast>(f: &Fdecl<'ast>, ctx: &Context<'ast>) -> Result<(), TypeError> {
    let mut locals: HashMap<Ident, Ty> = f.args.iter().map(|(t, n)| (*n, t.clone())).collect();

    let returns = block(&f.body, &f.ret_ty, &mut locals, ctx)?;

    if !returns {
        return Err(TypeError("function body must return a value".to_string()));
    }

    Ok(())
}

fn type_decl_verify<'ast>(t: &Tdecl<'ast>, ctx: &Context<'ast>) -> Result<(), TypeError> {
    for field in &t.fields {
        if let TyKind::Struct(s) = &field.ty.kind {
            if !ctx.structs.contains_key(s) {
                return Err(TypeError(format!("unknown struct {s} in struct field {} of struct {}", field.name, t.name)));
            }
        }
    }
    Ok(())
}

fn global<'ast>(g: &Gdecl<'ast>, ctx: &Context<'ast>) -> Result<(Ident<'ast>, Ty<'ast>), TypeError> {
    Ok((g.name, gexp(&g.init, ctx)?))
}

fn function_header<'ast>(f: &Fdecl<'ast>) -> Result<(Ident<'ast>, Ty<'ast>), TypeError> {
    // todo: not really a type error
    let set: HashSet<_> = f.args.iter().map(|(_, n)| n).collect();
    if set.len() != f.args.len() {
        return Err(TypeError("cannot have two function parameters with the same name".to_string()));
    }

    let ty = Ty { nullable: false, kind: TyKind::Fun(f.args.iter().map(|(t, _)| t).cloned().collect(), Box::new(f.ret_ty.clone())) };
    Ok((f.name, ty))
}

fn type_decl<'ast>(t: &Tdecl<'ast>) -> Result<Vec<(Ty<'ast>, Ident<'ast>)>, TypeError> {
    let fields: Vec<_> = t.fields.iter().map(|f| (f.ty.clone(), f.name)).collect();
    let distinct_fields: HashSet<_> = t.fields.iter().map(|f| &f.name).collect();
    if fields.len() != distinct_fields.len() {
        return Err(TypeError("duplicate struct field".to_string()));
    }
    Ok(fields)
}

pub fn check<'ast>(prog: &Prog<'ast>, arena: &'ast Arena<str>) -> Result<Context<'ast>, TypeError> {
    let mut structs: HashMap<Ident<'ast>, Vec<(Ty<'ast>, Ident<'ast>)>> = Default::default();
    let mut funcs: HashMap<Ident<'ast>, Ty<'ast>> = Default::default();

    for decl in prog {
        if let Decl::Type(t) = decl {
            let fields = type_decl(t)?;
            if structs.insert(t.name, fields).is_some() {
                return Err(TypeError(format!("a struct with name {} already exists", t.name)));
            }
        }
    }

    for (name, ty) in BUILTINS.iter() {
        assert!(funcs.insert(arena.intern(name), ty.clone()).is_none(), "function names can't conflict with type names");
    }

    for decl in prog {
        if let Decl::Fun(f) = decl {
            let (name, ty) = function_header(f)?;
            if let Some(n) = funcs.insert(name, ty) {
                return Err(TypeError(format!("a global function with name {} already exists", n)));
            }
        }
    }

    let mut context = Context {
        structs,
        vars: Default::default(),
        funcs,
    };

    for decl in prog {
        if let Decl::Var(v) = decl {
            let (name, ty) = global(v, &context)?;
            if let Some(n) = context.funcs.get(&name) {
                return Err(TypeError(format!("a global with name {} already exists", n)));
            }
            if let Some(n) = context.vars.insert(name, ty) {
                return Err(TypeError(format!("a global with name {} already exists", n)));
            }
        }
    }

    for decl in prog {
        match decl { 
            Decl::Fun(f) => function_body(f, &context)?,
            Decl::Type(t) => type_decl_verify(t, &context)?,
            _ => {},
        }
    }

    Ok(context)
}

