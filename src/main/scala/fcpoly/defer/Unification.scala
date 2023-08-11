package fcpoly.defer

case class PartialRenaming(
    cod: Level,
    dom: Level,
    map: Map[Level, Level],
    occ: Option[MetaID]
):
  def lift: PartialRenaming =
    PartialRenaming(cod + 1, dom + 1, map + (cod -> dom), occ)
  def skip: PartialRenaming =
    PartialRenaming(cod + 1, dom, map, occ)
  def withOcc(occ: MetaID): PartialRenaming =
    PartialRenaming(cod, dom, map, Some(occ))
  def nextCod: Val = Val.Var(cod)
  def getTermDirect(level: Level): Term =
    Term.Var(dom - level - 1)
  def getTerm(level: Level): Term =
    try getTermDirect(map(level))
    catch
      case _ =>
        throw InnerError.MetaRenameOutOfBound()

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

def pruneTy(prun: Pruning, ty: Val): Term =
  val (pr, remTy, tmMaker) = prun
    .foldRight((PartialRenaming(0, 0, Map(), None), ty, identity[Term]))(
      (mask, pair) =>
        val (pr, ty, tmMaker) = pair
        (ty.force, mask) match
          case (Val.Pi(param, ty, cl, icit), Mask.Keep(_)) =>
            def f(tm: Term) =
              tmMaker(Term.Pi(param, rename(pr, ty), tm, icit))
            (pr.lift, cl(pr.nextCod), f)
          case (Val.Pi(_, _, cl, _), Mask.Pruned) =>
            (pr.skip, cl(pr.nextCod), tmMaker)
          case _ => throw InnerError.PruningUnknownError()
    )
  tmMaker(rename(pr, remTy))

def pruneMeta(prun: Pruning, metaID: MetaID): Term =
  Meta.state(metaID) match
    case MetaState.Unsolved(ty) =>
      val prunedTy = eval(List(), pruneTy(prun, ty))
      val newMeta = Term.Meta(Meta.create(prunedTy))
      val boxed = lams(prun.length, ty, Term.Inserted(newMeta, prun))
      Meta.solve(metaID, eval(List(), boxed), ty)
      newMeta
    case MetaState.Solved(value, ty) =>
      throw InnerError.DuplicatedSolve("pruneMeta")

def pruneVFlex(pren: PartialRenaming, metaID: MetaID, spine: Spine): Term =
  Meta.state(metaID) match
    case MetaState.Unsolved(ty) =>
      var isRenaming = true
      var inScope = true
      val filtSp = spine.map { param =>
        param.value.force match
          case Val.Rigid(level, List()) =>
            pren.map.get(level) match
              case None      => inScope = false; (None, param.icit)
              case Some(lvl) => (Some(pren.getTermDirect(lvl)), param.icit)
          case value =>
            isRenaming = false
            (Some(rename(pren, value)), param.icit)
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

def rename(pr: PartialRenaming, value: Val): Term =
  def renameSp(spine: Spine, initialTerm: Term) =
    spine.foldRight(initialTerm)((param, term) =>
      Term.App(term, rename(pr, param.value), param.icit)
    )
  value.force match
    case Val.U =>
      Term.U
    case Val.Flex(rhs, spine) =>
      if pr.occ == Some(rhs) then throw InnerError.IntersectionRename()
      else pruneVFlex(pr, rhs, spine)
    case Val.Rigid(level, spine) =>
      renameSp(spine, pr.getTerm(level))
    case Val.Lam(param, cl, i) =>
      Term.Lam(param, rename(pr.lift, cl(pr.nextCod)), i)
    case Val.Pi(param, ty, cl, i) =>
      Term.Pi(param, rename(pr, ty), rename(pr.lift, cl(pr.nextCod)), i)

def solve(
    lhs: MetaID,
    pair: (PartialRenaming, Option[Pruning]),
    rhs: Val
): Unit =
  Meta.state(lhs) match
    case MetaState.Unsolved(ty) =>
      val (pren, prun) = pair
      prun match
        case None     => ty
        case Some(pr) => pruneTy(pr, ty)
      val tm = rename(pren.withOcc(lhs), rhs)
      val boxed = lams(pren.dom, ty, tm)
      Meta.solve(lhs, eval(List(), boxed), ty)
    case MetaState.Solved(_, _) => throw InnerError.DuplicatedSolve("solve")

def solve(lhs: MetaID, envLen: Level, sp: Spine, rhs: Val): Unit =
  solve(lhs, invert(envLen, sp), rhs)

def unifySp(envLen: Level, spx: Spine, spy: Spine) =
  if spx.length != spy.length then throw InnerError.SpineMismatch()
  spx.zip(spy).map((lhs, rhs) => unify(envLen, lhs.value, rhs.value))

def flexFlex(envLen: Level, mx: MetaID, spx: Spine, my: MetaID, spy: Spine) =
  def go(mx: MetaID, spx: Spine, my: MetaID, spy: Spine) =
    try
      val pren = invert(envLen, spx)
      solve(mx, pren, Val.Flex(my, spy))
    catch
      case _: InnerError =>
        solve(my, envLen, spy, Val.Flex(mx, spx))
  if spx.length > spy.length then go(mx, spx, my, spy) else go(my, spy, mx, spx)

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

def unifyCatch(ctx: Ctx, x: Val, y: Val): Unit =
  try unify(ctx.envLen, x, y)
  catch
    case e: InnerError =>
      throw InnerError.UnifyError(ctx, x.force, y.force, e)

// check if assumption `tm = ?metaID locals` can still be satisfied
def unifyPlaceholder(ctx: Ctx, tm: Term, metaID: MetaID): Unit =
  Meta.state(metaID) match
    case MetaState.Unsolved(ty) =>
      // meta is unsolved, use trivial lambdas as solution
      Meta.solve(metaID, eval(List(), Locals.toLams(ctx.locals, tm)), ty)
    case MetaState.Solved(value, ty) =>
      // meta is solved, apply locals first
      val fullVal = value(Env.filter(ctx.env, ctx.prun))
      // unify full value with original terms
      unifyCatch(ctx, eval(ctx.env, tm), fullVal)
