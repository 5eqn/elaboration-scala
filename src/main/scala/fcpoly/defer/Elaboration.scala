package fcpoly.defer

def insertActive(ctx: Ctx, tm: Term, ty: Val): (Term, Val) =
  try
    ty.force match
      case Val.Pi(param, ty, cl, Icit.Impl) =>
        val metaTerm = Meta.fresh(ctx, ty)
        val metaVal = eval(ctx.env, metaTerm)
        insertActive(ctx, Term.App(tm, metaTerm, Icit.Impl), cl(metaVal))
      case _ => (tm, ty)
  catch
    case e: InnerError =>
      throw InnerError.InsertError(ctx, tm, e)

def insertUntil(ctx: Ctx, name: Name, tm: Term, ty: Val): (Term, Val) =
  try
    ty.force match
      case Val.Pi(param, _, _, Icit.Impl) if param == name =>
        (tm, ty)
      case Val.Pi(param, ty, cl, Icit.Impl) =>
        val metaTerm = Meta.fresh(ctx, ty)
        val metaVal = eval(ctx.env, metaTerm)
        insertUntil(ctx, name, Term.App(tm, metaTerm, Icit.Impl), cl(metaVal))
      case _ => throw InnerError.ImplicitArgNotFound(name)
  catch
    case e: InnerError =>
      throw InnerError.InsertError(ctx, tm, e)

def insertPassive(ctx: Ctx, tm: Term, ty: Val): (Term, Val) = tm match
  case Term.Lam(_, _, Icit.Impl) =>
    (tm, ty)
  case _ => insertActive(ctx, tm, ty)

def infer(ctx: Ctx, tm: Raw): (Term, Val) =
  try
    tm match
      case Raw.U =>
        (Term.U, Val.U)
      case Raw.Hole =>
        val ty = eval(ctx.env, Meta.fresh(ctx, Val.U))
        (Meta.fresh(ctx, ty), ty)
      case Raw.Var(name) =>
        val (level, ty) = ctx(name)
        (Term.Var(ctx.envLen - level - 1), ty)
      case Raw.App(func, arg, dst) =>
        val i = dst.icit
        val (funcTerm, funcType) = dst match
          case Dst.Expl =>
            val (ttm, tty) = infer(ctx, func)
            insertActive(ctx, ttm, tty)
          case Dst.ImplAuto =>
            infer(ctx, func)
          case Dst.ImplBind(to) =>
            val (ttm, tty) = infer(ctx, func)
            insertUntil(ctx, to, ttm, tty)
        funcType.force match
          case Val.Pi(_, ty, cl, j) =>
            if i != j then throw InnerError.IcitMismatch(j, i)
            val argTerm = check(ctx, arg, ty)
            (Term.App(funcTerm, argTerm, i), cl(eval(ctx.env, argTerm)))
          case ty =>
            val argTy = eval(ctx.env, Meta.fresh(ctx, Val.U))
            val tmplCl =
              Closure(ctx.env, Meta.fresh(ctx.bind("x", argTy), Val.U))
            val tmplTy = Val.Pi("x", argTy, tmplCl, i)
            unifyCatch(ctx, ty, tmplTy)
            val argTerm = check(ctx, arg, argTy)
            (Term.App(funcTerm, argTerm, i), tmplCl(eval(ctx.env, argTerm)))
      case Raw.Lam(_, _, _, Src.ImplBind(_)) =>
        throw InnerError.InferNamedLambda()
      case Raw.Lam(param, mTy, body, src) =>
        val i = src.icit
        val lamTyTerm = mTy match
          case None     => Meta.fresh(ctx, Val.U)
          case Some(ty) => check(ctx, ty, Val.U)
        val lamTyVal = eval(ctx.env, lamTyTerm)
        val newCtx = ctx.bind(param, lamTyVal)
        val (ttm, tty) = infer(newCtx, body)
        val (bodyTerm, bodyType) = insertPassive(newCtx, ttm, tty)
        val tyClosure = Closure(ctx.env, quote(ctx.envLen + 1, bodyType))
        (Term.Lam(param, bodyTerm, i), Val.Pi(param, lamTyVal, tyClosure, i))
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
        val (nextTerm, nextTy) =
          infer(ctx.define(name, bodyVal, tyVal, bodyTerm, tyTerm), next)
        (Term.Let(name, tyTerm, bodyTerm, nextTerm), nextTy)
  catch
    case e: InnerError =>
      throw new RootError(ctx, tm, e)

def check(ctx: Ctx, tm: Raw, ty: Val): Term =
  try
    val lamMatch = (src: Src, piParam: Name, i: Icit) =>
      src match
        case Src.ImplBind(from) => from == piParam && i == Icit.Impl
        case _                  => src.icit == i
    (tm, ty.force) match
      case (Raw.Hole, ty) =>
        Meta.fresh(ctx, ty)
      case (Raw.Lam(param, mLamTy, body, src), Val.Pi(piParam, ty, cl, i))
          if lamMatch(src, piParam, i) =>
        mLamTy match
          case None =>
          case Some(lamTy) =>
            val lamTyTerm = check(ctx, lamTy, Val.U)
            unifyCatch(ctx, eval(ctx.env, lamTyTerm), ty)
        val paramVal = ctx.nextVal
        val bodyVal = check(ctx.bind(param, paramVal, ty), body, cl(paramVal))
        Term.Lam(param, bodyVal, i)
      case (_, Val.Pi(param, ty, cl, Icit.Impl)) =>
        val paramVal = ctx.nextVal
        val bodyVal = check(ctx.bind(param, paramVal, ty), tm, cl(paramVal))
        Term.Lam(param, bodyVal, Icit.Impl)
      // delay checking if ty is unknown
      case (_, ty @ Val.Flex(_, _)) =>
        val checkID = Check.create(ctx, tm, ty)
        Term.Unchecked(checkID)
      case (tm, expected) =>
        val (tm2, tty) = infer(ctx, tm)
        val (tm3, inferred) = insertPassive(ctx, tm2, tty)
        unifyCatch(ctx, expected, inferred)
        tm3
  catch
    case e: InnerError =>
      throw new RootError(ctx, tm, e)