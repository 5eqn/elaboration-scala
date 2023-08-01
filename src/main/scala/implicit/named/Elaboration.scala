package `implicit`.named

def insertActive(ctx: Ctx, tm: Term, ty: Val): (Term, Val) = ty.force match
  case Val.Pi(param, ty, cl, Icit.Impl) =>
    val metaTerm = Meta.fresh
    val metaVal = eval(ctx.env, metaTerm)
    insertActive(ctx, Term.App(tm, metaTerm, Icit.Impl), cl(metaVal))
  case _ => (tm, ty)

def insertUntil(ctx: Ctx, name: Name, tm: Term, ty: Val): (Term, Val) =
  ty.force match
    // stop recursing if name match
    // observe the trivial case where
    // f : {A} -> A -> A, f {A = Int} 0
    // obviously nothing should be inserted
    case Val.Pi(param, _, _, Icit.Impl) if param == name =>
      (tm, ty)
    case Val.Pi(param, ty, cl, Icit.Impl) =>
      val metaTerm = Meta.fresh
      val metaVal = eval(ctx.env, metaTerm)
      insertUntil(ctx, name, Term.App(tm, metaTerm, Icit.Impl), cl(metaVal))
    // disallow unfruitful insertion
    // e.g. `f : {A} -> A -> A, f {X = Int}` fails
    // because {X} is not found
    case _ => throw new Exception(s"can't find named implicit $name")

def insertPassive(ctx: Ctx, tm: Term, ty: Val): (Term, Val) = tm match
  case Term.Lam(_, _, Icit.Impl) =>
    (tm, ty)
  case _ => insertActive(ctx, tm, ty)

def infer(ctx: Ctx, tm: Raw): (Term, Val) = tm match
  case Raw.U =>
    (Term.U, Val.U)
  case Raw.Hole =>
    (Meta.fresh, eval(ctx.env, Meta.fresh))
  case Raw.Var(name) =>
    (Term.Var(ctx.envLen - ctx.getLevel(name) - 1), ctx.getType(name))
  case Raw.App(func, arg, dst) =>
    val i = dst.icit
    val (funcTerm, funcType) = dst match
      case Dst.Expl =>
        val (ttm, tty) = infer(ctx, func)
        insertActive(ctx, ttm, tty)
      case Dst.ImplAuto =>
        infer(ctx, func)
      // when dealing with named implicit argument,
      // insert until the argument name is found
      // note how we disallow reverse-order assigning
      case Dst.ImplBind(to) =>
        val (ttm, tty) = infer(ctx, func)
        insertUntil(ctx, to, ttm, tty)
    funcType.force match
      case Val.Pi(_, ty, cl, j) =>
        if i != j then throw new Exception(s"can't apply $i to $j Pi")
        val argTerm = check(ctx, arg, ty)
        (Term.App(funcTerm, argTerm, i), cl(eval(ctx.env, argTerm)))
      case ty =>
        val argTy = eval(ctx.env, Meta.fresh)
        val tmplCl = Closure(ctx.env, Meta.fresh)
        val tmplTy = Val.Pi("x", argTy, tmplCl, i)
        unify(ctx.envLen, ty, tmplTy)
        val argTerm = check(ctx, arg, argTy)
        (Term.App(funcTerm, argTerm, i), tmplCl(eval(ctx.env, argTerm)))
  case Raw.Lam(_, _, Src.ImplBind(_)) =>
    throw new Exception("type of named lambda can't be inferred")
  case Raw.Lam(param, body, src) =>
    val i = src.icit
    val metaVal = eval(ctx.env, Meta.fresh)
    val newCtx = ctx.add(param, metaVal)
    val (ttm, tty) = infer(newCtx, body)
    val (bodyTerm, bodyType) = insertPassive(newCtx, ttm, tty)
    val tyClosure = Closure(ctx.env, quote(ctx.envLen + 1, bodyType))
    (Term.Lam(param, bodyTerm, i), Val.Pi(param, metaVal, tyClosure, i))
  case Raw.Pi(param, ty, body, i) =>
    val tyTerm = check(ctx, ty, Val.U)
    val tyVal = eval(ctx.env, tyTerm)
    val bodyTerm = check(ctx.add(param, tyVal), body, Val.U)
    (Term.Pi(param, tyTerm, bodyTerm, i), Val.U)
  case Raw.Let(name, ty, body, next) =>
    val tyTerm = check(ctx, ty, Val.U)
    val tyVal = eval(ctx.env, tyTerm)
    val bodyTerm = check(ctx, body, tyVal)
    val bodyVal = eval(ctx.env, bodyTerm)
    val (nextTerm, nextTy) = infer(ctx.add(name, bodyVal, tyVal), next)
    (Term.Let(name, tyTerm, bodyTerm, nextTerm), nextTy)

def check(ctx: Ctx, tm: Raw, ty: Val): Term =
  val lamMatch = (src: Src, piParam: Name, i: Icit) =>
    src match
      case Src.ImplBind(from) => from == piParam && i == Icit.Impl
      case _                  => src.icit == i
  (tm, ty.force) match
    case (Raw.Hole, _) =>
      Meta.fresh
    // disallow match of different names
    // e.g. in `f : {A} {B} A -> A, f = \{B = Alias} a. a`,
    // `f` will be elaborated to `\{?A} {B = Alias} a. a`
    case (Raw.Lam(param, body, src), Val.Pi(piParam, ty, cl, i))
        if lamMatch(src, piParam, i) =>
      val paramVal = ctx.nextVal
      val bodyVal = check(ctx.add(param, paramVal, ty), body, cl(paramVal))
      Term.Lam(param, bodyVal, i)
    case (_, Val.Pi(param, ty, cl, Icit.Impl)) =>
      val paramVal = ctx.nextVal
      val bodyVal = check(ctx.add(s"?$param", paramVal, ty), tm, cl(paramVal))
      Term.Lam(param, bodyVal, Icit.Impl)
    case _ =>
      val (ttm, tty) = infer(ctx, tm)
      val (term, value) = insertPassive(ctx, ttm, tty)
      unify(ctx.envLen, value, ty)
      term
