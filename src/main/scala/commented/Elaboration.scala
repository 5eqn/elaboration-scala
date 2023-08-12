package commented

/*
 * INSERT
 */

// When applying a explicit term like `f x`,
// but if `f` takes implicit argument,
// we need to insert meta terms until the next argument is explicit.
//
// For example, if `f : {A : U} -> {a : A} -> (x : A)`,
// `f x` should be elaborated to `f _ _ x`.
//
// Note that if `f` is an implicit lambda,
// meta terms should still be inserted!
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

// Insert until given name.
//
// Stop recursing if name match,
// observe the trivial case where
// f : {A} -> A -> A, f {A = Int} 0
// obviously nothing should be inserted.
//
// Disallow unfruitful insertion,
// e.g. `f : {A} -> A -> A, f {X = Int}` fails
// because {X} is not found.
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

// When forming a lambda, or checking implicit function against
// explicit Pi type, e.g. `id: {A} -> A -> A` against `A -> A`,
// the body term shouldn't depend on future context.
//
// Formally, in `Γ ⊢ f` if `f` takes implicit argument,
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

/*
 * INFER
 */

// infer type of given raw term, return elaborated result as well
def infer(ctx: Ctx, tm: Raw): (Term, Val) =
  try
    tm match
      // U : U
      case Raw.U =>
        (Term.U, Val.U)
      // _ : ?0 [ctx], _ = ?1 [ctx]
      case Raw.Hole =>
        val ty = eval(ctx.env, Meta.fresh(ctx, Val.U))
        (Meta.fresh(ctx, ty), ty)
      // direct from nameMap
      case Raw.Var(name) =>
        val (level, ty) = ctx(name)
        (Term.Var(ctx.envLen - level - 1), ty)
      // insert until icit match,
      // func : (x : Ty) -> Cl x, arg : Ty
      //      ==> func arg : Cl arg
      // func : Ty, Ty = (x : ?0 [ctx]) -> ?1 [ctx] x, arg : ?0 [ctx]
      //      ==> func arg : ?1 [ctx] arg
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
            unifyCatch(ctx, tmplTy, ty)
            val argTerm = check(ctx, arg, argTy)
            (Term.App(funcTerm, argTerm, i), tmplCl(eval(ctx.env, argTerm)))
      // named lambda makes sense only when corresponding Pi type exists
      case Raw.Lam(_, _, _, Src.ImplBind(_)) =>
        throw InnerError.InferNamedLambda()
      // insert implicit arguments for body, and
      // body : Body param
      //      ==> \param. body : (param : ?0 [ctx]) -> Body param
      // Ty   : U, body : Body param
      //      ==> \(param : Ty). body : (param : Ty) -> Body param
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
      // Ty : U, Body param : U ==> (param : Ty) -> Body : U
      case Raw.Pi(param, ty, body, i) =>
        val tyTerm = check(ctx, ty, Val.U)
        val tyVal = eval(ctx.env, tyTerm)
        val bodyTerm = check(ctx.bind(param, tyVal), body, Val.U)
        (Term.Pi(param, tyTerm, bodyTerm, i), Val.U)
      // Ty : U, body : Ty ==> add (body : Ty) to context of next
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

/*
 * CHECK
 */

// check if given raw term has given type, and return elaborated result
def check(ctx: Ctx, tm: Raw, ty: Val): Term =
  def isUnknown(v: Val) = v match
    case Val.Flex(_, _) => true
    case _              => false
  try
    val lamMatch = (src: Src, piParam: Name, i: Icit) =>
      src match
        case Src.ImplBind(from) => from == piParam && i == Icit.Impl
        case _                  => src.icit == i
    (tm, ty.force) match
      // _ : Ty, _ = ?0 [ctx]
      case (Raw.Hole, ty) =>
        Meta.fresh(ctx, ty)
      // if icit match,
      // body : Cl param, (param : Ty) ==> \param. body : (param : Ty) -> Cl param
      // LamTy : U, LamTy = Ty, ...    ==> \(param : LamTy). body : ...
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
      // if we check `x : {A} -> A` when `x : _`,
      // we solve `_` to `{A} -> A`, instead of inserting implicit argument
      // According to elab-zoo, "this is a modest but useful approximation of
      // polymorphic argument inference."
      case (tm @ Raw.Var(name), ty @ Val.Pi(_, _, _, Icit.Impl))
          if (ctx(name)._2.force match
            case Val.Flex(_, _) => true
            case _              => false
          ) =>
        val (lvl, varTy) = ctx(name)
        unify(ctx.envLen, varTy.force, ty)
        Term.Var(ctx.envLen - lvl - 1)
      // otherwise insert implicit lambda
      // x : {param : Ty} -> Cl param, x = \{param}. body
      case (tm, Val.Pi(param, ty, cl, Icit.Impl)) =>
        val paramVal = ctx.nextVal
        val bodyVal = check(ctx.bind(param, paramVal, ty), tm, cl(paramVal))
        Term.Lam(param, bodyVal, Icit.Impl)
      // defer checking term against unknown type until it's solved
      // e.g. check `\x y. x : ?0 [ctx]` will be deferred,
      // because `?0 [ctx]` can be solved to start with implicit Pi
      case (tm, ty @ Val.Flex(metaID, _)) =>
        val checkID = Check.create(ctx, tm, ty)
        Meta.transfer(metaID, checkID)
        Term.Unchecked(checkID)
      // tm : Inferred, Inferred = Expected ==> tm : Expected
      case (tm, expected) =>
        val (tm2, tty) = infer(ctx, tm)
        val (tm3, inferred) = insertPassive(ctx, tm2, tty)
        unifyCatch(ctx, expected, inferred)
        tm3
  catch
    case e: InnerError =>
      throw new RootError(ctx, tm, e)
