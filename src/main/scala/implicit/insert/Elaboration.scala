package `implicit`.insert

// When applying a explicit term like `f x`,
// but if `f` takes implicit argument,
// we need to insert meta terms until the next argument is explicit.
//
// For example, if `f : {A : U} -> {a : A} -> (x : A)`,
// `f x` should be elaborated to `f _ _ x`.
//
// Note that if `f` is an implicit lambda,
// meta terms should still be inserted!
def insertActive(ctx: Ctx, tm: Term, ty: Val): (Term, Val) = ty.force match
  case Val.Pi(param, ty, cl, Icit.Impl) =>
    val metaTerm = Meta.fresh(ctx)
    val metaVal = eval(ctx.env, metaTerm)
    insertActive(ctx, Term.App(tm, metaTerm, Icit.Impl), cl(metaVal))
  case _ => (tm, ty)

// When forming a lambda, or checking implicit function against
// explicit Pi type, e.g. `id: {A} -> A -> A` against `A -> A`,
// the body term shouldn't depend on future context.
//
// Formally, in `Γ |- f` if `f` takes implicit argument,
// the argument's scope is only `Γ`, containing global context and
// lambda arguments (if any), thus we need to insert meta terms
// before future context emerges.
//
// Note that if `f` is an implicit lambda,
// the implicit argument can bind to future context,
// so there's no need to immediately insert meta terms!
def insertPassive(ctx: Ctx, tm: Term, ty: Val): (Term, Val) = tm match
  case Term.Lam(_, _, Icit.Impl) =>
    (tm, ty)
  case _ => insertActive(ctx, tm, ty)

def infer(ctx: Ctx, tm: Raw): (Term, Val) = tm match
  case Raw.U =>
    (Term.U, Val.U)
  case Raw.Hole =>
    (Meta.fresh(ctx), eval(ctx.env, Meta.fresh(ctx)))
  case Raw.Var(name) =>
    (Term.Var(ctx.envLen - ctx.getLevel(name) - 1), ctx.getType(name))
  case Raw.App(func, arg, dst) =>
    val i = dst.icit
    val (funcTerm, funcType) = dst match
      case Dst.Expl =>
        val (ttm, tty) = infer(ctx, func)
        // insert implicit args actively before explicit application
        insertActive(ctx, ttm, tty)
      case Dst.ImplAuto =>
        infer(ctx, func)
      // implement in next chapter
      case Dst.ImplBind(to) => throw new Exception("explode")
    funcType.force match
      case Val.Pi(_, ty, cl, j) =>
        if i != j then throw new Exception(s"can't apply $i to $j Pi")
        val argTerm = check(ctx, arg, ty)
        (Term.App(funcTerm, argTerm, i), cl(eval(ctx.env, argTerm)))
      case ty =>
        val argTy = eval(ctx.env, Meta.fresh(ctx))
        val tmplCl = Closure(ctx.env, Meta.fresh(ctx.bind("x", argTy)))
        val tmplTy = Val.Pi("x", argTy, tmplCl, i)
        unify(ctx.envLen, ty, tmplTy)
        val argTerm = check(ctx, arg, argTy)
        (Term.App(funcTerm, argTerm, i), tmplCl(eval(ctx.env, argTerm)))
  // type of named lambda can't be inferred
  case Raw.Lam(_, _, Src.ImplBind(_)) =>
    throw new Exception("type of named lambda can't be inferred")
  case Raw.Lam(param, body, src) =>
    val i = src.icit
    val metaVal = eval(ctx.env, Meta.fresh(ctx))
    val newCtx = ctx.bind(param, metaVal)
    val (ttm, tty) = infer(newCtx, body)
    // insert implicit args passively for lambda body
    val (bodyTerm, bodyType) = insertPassive(newCtx, ttm, tty)
    val tyClosure = Closure(ctx.env, quote(ctx.envLen + 1, bodyType))
    (Term.Lam(param, bodyTerm, i), Val.Pi(param, metaVal, tyClosure, i))
  case Raw.Pi(param, ty, body, i) =>
    val tyTerm = check(ctx, ty, Val.U)
    val tyVal = eval(ctx.env, tyTerm)
    val bodyTerm = check(ctx.bind(param, tyVal), body, Val.U)
    (Term.Pi(param, tyTerm, bodyTerm, i), Val.U)
  case Raw.Let(name, ty, body, next) =>
    val tyTerm = check(ctx, ty, Val.U)
    val tyVal = eval(ctx.env, tyTerm)
    val bodyTerm = check(ctx, body, tyVal)
    val bodyVal = eval(ctx.env, bodyTerm)
    val (nextTerm, nextTy) = infer(ctx.define(name, bodyVal, tyVal), next)
    (Term.Let(name, tyTerm, bodyTerm, nextTerm), nextTy)

def check(ctx: Ctx, tm: Raw, ty: Val): Term = (tm, ty.force) match
  case (Raw.Hole, _) =>
    Meta.fresh(ctx)
  // if icit match, check as usual
  // e.g. in `id : {A : U} -> A -> A = \{A} x. x`,
  // two icits match
  case (Raw.Lam(param, body, src), Val.Pi(_, ty, cl, i)) if (src.icit == i) =>
    val paramVal = ctx.nextVal
    val bodyVal = check(ctx.bind(param, paramVal, ty), body, cl(paramVal))
    Term.Lam(param, bodyVal, i)
  // if they don't match and pi is implicit,
  // add a implicit term to lambda
  // e.g. `id : {A : U} -> A -> A = \{auto insert ?A} x. x`,
  // name has prefix "?" to avoid name collision
  case (_, Val.Pi(param, ty, cl, Icit.Impl)) =>
    val paramVal = ctx.nextVal
    val bodyVal = check(ctx.bind(s"?$param", paramVal, ty), tm, cl(paramVal))
    Term.Lam(param, bodyVal, Icit.Impl)
  case _ =>
    val (ttm, tty) = infer(ctx, tm)
    // insert implicit args passively for surface variable
    val (term, value) = insertPassive(ctx, ttm, tty)
    unify(ctx.envLen, value, ty)
    term
