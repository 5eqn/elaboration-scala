package `implicit`.modularize

def infer(ctx: Ctx, tm: Raw): (Term, Val) = tm match
  case Raw.U =>
    (Term.U, Val.U)
  case Raw.Hole =>
    (Meta.fresh, eval(ctx.env, Meta.fresh))
  case Raw.Var(name) =>
    (Term.Var(ctx.envLen - ctx.getLevel(name) - 1), ctx.getType(name))
  case Raw.App(func, arg) =>
    val (funcTerm, funcType) = infer(ctx, func)
    funcType.force match
      case Val.Pi(_, ty, cl) =>
        val argTerm = check(ctx, arg, ty)
        (Term.App(funcTerm, argTerm), cl(eval(ctx.env, argTerm)))
      case ty =>
        val argTy = eval(ctx.env, Meta.fresh)
        val tmplCl = Closure(ctx.env, Meta.fresh)
        val tmplTy = Val.Pi("x", argTy, tmplCl)
        unify(ctx.envLen, ty, tmplTy)
        val argTerm = check(ctx, arg, argTy)
        (Term.App(funcTerm, argTerm), tmplCl(eval(ctx.env, argTerm)))
  case Raw.Lam(param, body) =>
    val metaVal = eval(ctx.env, Meta.fresh)
    val (bodyTerm, bodyType) = infer(ctx.add(param, metaVal), body)
    val tyClosure = Closure(ctx.env, quote(ctx.envLen + 1, bodyType))
    (Term.Lam(param, bodyTerm), Val.Pi(param, metaVal, tyClosure))
  case Raw.Pi(param, ty, body) =>
    val tyTerm = check(ctx, ty, Val.U)
    val tyVal = eval(ctx.env, tyTerm)
    val bodyTerm = check(ctx.add(param, tyVal), body, Val.U)
    (Term.Pi(param, tyTerm, bodyTerm), Val.U)
  case Raw.Let(name, ty, body, next) =>
    val tyTerm = check(ctx, ty, Val.U)
    val tyVal = eval(ctx.env, tyTerm)
    val bodyTerm = check(ctx, body, tyVal)
    val bodyVal = eval(ctx.env, bodyTerm)
    val (nextTerm, nextTy) = infer(ctx.add(name, bodyVal, tyVal), next)
    (Term.Let(name, tyTerm, bodyTerm, nextTerm), nextTy)

def check(ctx: Ctx, tm: Raw, ty: Val): Term = (tm, ty.force) match
  case (Raw.Hole, _) =>
    Meta.fresh
  case (Raw.Lam(param, body), Val.Pi(_, ty, cl)) =>
    val value = ctx.nextVal
    val bodyVal = check(ctx.add(param, value, ty), body, cl(value))
    Term.Lam(param, bodyVal)
  case _ =>
    val (term, value) = infer(ctx, tm)
    unify(ctx.envLen, value, ty)
    term
