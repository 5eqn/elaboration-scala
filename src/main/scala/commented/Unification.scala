package commented

/*
 * RENAME
 */

// A partial renaming on value.
case class PartialRenaming(
    cod: Level,
    dom: Level,
    map: Map[Level, Level],
    occ: Option[MetaID]
):
  // keep the next variable
  def lift: PartialRenaming =
    PartialRenaming(cod + 1, dom + 1, map + (cod -> dom), occ)

  // skip the next variable
  def skip: PartialRenaming =
    PartialRenaming(cod + 1, dom, map, occ)

  // add occlusion of meta to this partial renaming,
  // to prevent solving recursive meta like ?0 = ... ?0
  def withOcc(occ: MetaID): PartialRenaming =
    PartialRenaming(cod, dom, map, Some(occ))
  def nextCod: Val = Val.Var(cod)

  // prune duplicated arg from meta which is a renaming
  // e.g. "keep a, b" for `?0 a b c` generates `?0 = \a b c. ?1 a b`,
  // discarding param `c` from `?0`
  def pruneVFlex(metaID: MetaID, spine: Spine): Term =
    Meta.state(metaID) match
      case MetaState.Unsolved(_, _) =>
        var isRenaming = true
        var inScope = true
        val filtSp = spine.map { param =>
          param.value.force match
            case Val.Rigid(level, List()) =>
              map.get(level) match
                case None      => inScope = false; (None, param.icit)
                case Some(lvl) => (Some(Term.Var(dom - level - 1)), param.icit)
            case value =>
              isRenaming = false
              (Some(rename(value)), param.icit)
        }
        if !isRenaming && !inScope then throw InnerError.PruneNonRenaming()
        val newMeta =
          if inScope then Term.Meta(metaID)
          else
            val prun = filtSp.map {
              case (None, _)    => Mask.Pruned
              case (Some(_), i) => Mask.Keep(i)
            }
            pruneMeta(prun, metaID)
        filtSp.foldRight(newMeta)((pair, tm) =>
          val (opt, icit) = pair
          opt match
            case None        => tm
            case Some(value) => Term.App(tm, value, icit)
        )
      case MetaState.Solved(value, ty) =>
        throw InnerError.DuplicatedSolve("pruneVFlex")

  // rename a value
  def rename(value: Val): Term =
    def renameSp(spine: Spine, initialTerm: Term) =
      spine.foldRight(initialTerm)((param, term) =>
        Term.App(term, rename(param.value), param.icit)
      )
    value.force match
      case Val.U =>
        Term.U
      case Val.Flex(rhs, spine) =>
        if occ == Some(rhs) then throw InnerError.IntersectionRename()
        else pruneVFlex(rhs, spine)
      case Val.Rigid(level, spine) =>
        map.get(level) match
          case None        => throw InnerError.MetaRenameOutOfBound()
          case Some(value) => renameSp(spine, Term.Var(dom - level - 1))
      case Val.Lam(param, cl, i) =>
        Term.Lam(param, lift.rename(cl(nextCod)), i)
      case Val.Pi(param, ty, cl, i) =>
        Term.Pi(param, rename(ty), lift.rename(cl(nextCod)), i)

/*
 * PRUNE
 */

// wrap a term in lambdas according to given ty
def lams(mxLvl: Level, ty: Val, initTm: Term): Term =
  def go(ty: Val, lvl: Level): Term =
    if lvl == mxLvl then initTm
    else
      ty.force match
        case Val.Pi(param, ty, cl, icit) =>
          val newName = if param == "_" then "x" + lvl else param
          Term.Lam(newName, go(cl(Val.Var(lvl)), lvl + 1), icit)
        case _ => throw InnerError.PruningUnknownError()
  go(ty, 0)

// prune specified Pi entries from a type
def pruneTy(prun: Pruning, ty: Val): Term =
  val (pr, remTy, tmMaker) = prun
    .foldRight((PartialRenaming(0, 0, Map(), None), ty, identity[Term]))(
      (mask, pair) =>
        val (pr, ty, tmMaker) = pair
        (ty.force, mask) match
          case (Val.Pi(param, ty, cl, icit), Mask.Keep(_)) =>
            def f(tm: Term) =
              tmMaker(Term.Pi(param, pr.rename(ty), tm, icit))
            (pr.lift, cl(pr.nextCod), f)
          case (Val.Pi(_, _, cl, _), Mask.Pruned) =>
            (pr.skip, cl(pr.nextCod), tmMaker)
          case _ => throw InnerError.PruningUnknownError()
    )
  tmMaker(pr.rename(remTy))

// prune Pi entries for a meta and solve it,
// e.g. prune `c : C` from `?0 : A -> B -> C -> X` yields
// `?0 = \a b c. ?1 a b`
def pruneMeta(prun: Pruning, metaID: MetaID): Term =
  Meta.state(metaID) match
    case MetaState.Unsolved(blk, ty) =>
      val prunedTy = eval(List(), pruneTy(prun, ty))
      val newMeta = Term.Meta(Meta.create(prunedTy, blk))
      val boxed = lams(prun.length, ty, Term.Inserted(newMeta, prun))
      Meta.solve(metaID, eval(List(), boxed), ty)
      newMeta
    case MetaState.Solved(value, ty) =>
      throw InnerError.DuplicatedSolve("pruneMeta")

/*
 * SOLVE
 */

// generate partial renaming from a spine,
// removing duplicates (don't remove first occurence?)
def invert(envLen: Level, spine: Spine): (PartialRenaming, Option[Pruning]) =
  var domVars = Set[Level]()
  var ren = Map[Level, Level]()
  var prun = List[Mask]()
  var isLinear = true
  var dom = 0
  spine.reverse.foreach { param =>
    param.value.force match
      case Val.Rigid(level, List()) =>
        if domVars.contains(level)
        then
          ren -= level
          prun = Mask.Pruned :: prun
          isLinear = false
        else
          ren += (level -> dom)
          domVars += level
          prun = Mask.Keep(param.icit) :: prun
        dom += 1
      case _ =>
        throw InnerError.InvertNonRenaming()
  }
  val pren = PartialRenaming(envLen, dom, ren, None)
  if isLinear then (pren, None) else (pren, Some(prun))

// solve `Γ ⊢ ?lhs spine =? rhs` with known renaming
def solve(
    lhs: MetaID,
    pair: (PartialRenaming, Option[Pruning]),
    rhs: Val
): Unit =
  Meta.state(lhs) match
    case MetaState.Unsolved(blk, ty) =>
      val (pren, prun) = pair
      prun match
        case None     => ty
        case Some(pr) => pruneTy(pr, ty)
      val tm = pren.withOcc(lhs).rename(rhs)
      val boxed = lams(pren.dom, ty, tm)
      Meta.solve(lhs, eval(List(), boxed), ty)
      Check.retryAll(blk)
    case MetaState.Solved(_, _) => throw InnerError.DuplicatedSolve("solve")

// solve `Γ ⊢ ?lhs spine =? rhs`
def solve(lhs: MetaID, envLen: Level, sp: Spine, rhs: Val): Unit =
  solve(lhs, invert(envLen, sp), rhs)

// solve (Γ ⊢ ?mx spx =? ?my spy`
// prefer invertible spine and longer (inner) spine
def flexFlex(envLen: Level, mx: MetaID, spx: Spine, my: MetaID, spy: Spine) =
  def go(mx: MetaID, spx: Spine, my: MetaID, spy: Spine) =
    try
      val pren = invert(envLen, spx)
      solve(mx, pren, Val.Flex(my, spy))
    catch
      case _: InnerError =>
        solve(my, envLen, spy, Val.Flex(mx, spx))
  if spx.length > spy.length then go(mx, spx, my, spy) else go(my, spy, mx, spx)

// solve `Γ ⊢ ?0 spx =? ?0 spy`
// non renaming => unifySp
// renaming => keep intersection only
def intersect(envLen: Level, metaID: MetaID, spx: Spine, spy: Spine) =
  var isRenaming = true
  val prun = spx
    .zip(spy)
    .map((lhs, rhs) =>
      (lhs.value.force, rhs.value.force) match
        case (Val.Rigid(lvx, List()), Val.Rigid(lvy, List())) =>
          if lvx == lvy then Mask.Keep(lhs.icit) else Mask.Pruned
        case _ => isRenaming = false; Mask.Pruned
    )
  if isRenaming then pruneMeta(prun, metaID) else unifySp(envLen, spx, spy)

/*
 * UNIFY
 */

// unify two spines
def unifySp(envLen: Level, spx: Spine, spy: Spine) =
  if spx.length != spy.length then throw InnerError.SpineMismatch()
  spx.zip(spy).map((lhs, rhs) => unify(envLen, lhs.value, rhs.value))

// unify x and y
def unify(envLen: Level, x: Val, y: Val): Unit =
  (x.force, y.force) match
    case (Val.U, Val.U) =>
    case (Val.Flex(x, spx), Val.Flex(y, spy)) if x == y =>
      intersect(envLen, x, spx, spy)
    case (Val.Flex(x, spx), Val.Flex(y, spy)) =>
      flexFlex(envLen, x, spx, y, spy)
    case (Val.Rigid(x, spx), Val.Rigid(y, spy)) if x == y =>
      unifySp(envLen, spx, spy)
    case (Val.Flex(id, spine), y) => solve(id, envLen, spine, y)
    case (x, Val.Flex(id, spine)) => solve(id, envLen, spine, x)
    case (Val.Lam(param, cl, i), y) =>
      val value = Val.Var(envLen)
      unify(envLen + 1, cl(value), y(Param(value, i)))
    case (x, Val.Lam(param, cl, i)) =>
      val value = Val.Var(envLen)
      unify(envLen + 1, x(Param(value, i)), cl(value))
    case (Val.Pi(param1, ty1, cl1, i1), Val.Pi(param2, ty2, cl2, i2)) =>
      if i1 != i2 then throw InnerError.IcitMismatch(i1, i2)
      val value = Val.Var(envLen)
      unify(envLen, ty1, ty2)
      unify(
        envLen + 1,
        cl1(value),
        cl2(value)
      )
    case _ => throw InnerError.PlainUnifyError()

// unify with contextual error catching
def unifyCatch(ctx: Ctx, x: Val, y: Val): Unit =
  try unify(ctx.envLen, x, y)
  catch
    case e: InnerError =>
      throw InnerError.UnifyError(ctx, x.force, y.force, e)

// optimize unify behaviour for placeholder
// because unifying `tm ?= ?metaID [ctx]` has
// trivial solution `?metaID = \[ctx]. tm`
def unifyPlaceholder(ctx: Ctx, tm: Term, metaID: MetaID): Unit =
  Meta.state(metaID) match
    case MetaState.Unsolved(blk, ty) =>
      Meta.solve(metaID, eval(List(), Locals.toLams(ctx.locals, tm)), ty)
      Check.retryAll(blk)
    case MetaState.Solved(value, ty) =>
      val fullVal = value(Env.filter(ctx.env, ctx.prun))
      unifyCatch(ctx, eval(ctx.env, tm), fullVal)
