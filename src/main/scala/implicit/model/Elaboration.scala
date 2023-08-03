package `implicit`.model

def infer(ctx: Ctx, tm: Raw): (Term, Val) = tm match
  case Raw.U =>
    (Term.U, Val.U)
  case Raw.Hole =>
    (Meta.fresh(ctx), eval(ctx.env, Meta.fresh(ctx)))
  case Raw.Var(name) =>
    val (level, ty) = ctx.src(name)
    (Term.Var(ctx.envLen - level - 1), ty)
  case Raw.App(func, arg, dst) =>
    // elaborate in later chapters
    // note how icit is passed passively,
    // there will be more similar cases afterwards
    val i = dst.icit
    val (funcTerm, funcType) = infer(ctx, func)
    funcType.force match
      // check icit consistency here
      case Val.Pi(_, ty, cl, j) =>
        if i != j then throw new Exception(s"icit inconsistency when app $i")
        val argTerm = check(ctx, arg, ty)
        (Term.App(funcTerm, argTerm, i), cl(eval(ctx.env, argTerm)))
      case ty =>
        val argTy = eval(ctx.env, Meta.fresh(ctx))
        val tmplCl = Closure(ctx.env, Meta.fresh(ctx.bind("x", argTy)))
        val tmplTy = Val.Pi("x", argTy, tmplCl, i)
        unify(ctx.envLen, ty, tmplTy)
        val argTerm = check(ctx, arg, argTy)
        (Term.App(funcTerm, argTerm, i), tmplCl(eval(ctx.env, argTerm)))
  case Raw.Lam(param, body, src) =>
    // elaborate in later chapters
    val i = src.icit
    val metaVal = eval(ctx.env, Meta.fresh(ctx))
    val (bodyTerm, bodyType) = infer(ctx.bind(param, metaVal), body)
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
  case (Raw.Lam(param, body, src), Val.Pi(_, ty, cl, i)) =>
    // elaborate in later chapters
    val value = ctx.nextVal
    val bodyVal = check(ctx.bind(param, value, ty), body, cl(value))
    Term.Lam(param, bodyVal, i)
  case _ =>
    val (term, value) = infer(ctx, tm)
    unify(ctx.envLen, value, ty)
    term
