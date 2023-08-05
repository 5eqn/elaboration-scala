package prune.scope

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
  // direct access to term
  def getTermDirect(level: Level): Term =
    Term.Var(dom - level - 1)
  def getTerm(level: Level): Term =
    try Term.Var(dom - map(level) - 1)
    catch
      case _ =>
        throw InnerError.MetaRenameOutOfBound()

// prunes pi arguments from ty,
// for example pruning B from A -> B -> C yields A -> C
// tail-recursive implementation, very similar to the haskell original
def pruneTy(prun: Pruning, ty: Val): Term =
  // pren converts ty to our term, but it's not surjective
  def go(prun: Pruning, pren: PartialRenaming, ty: Val): Term =
    // reverse the pruning so that the first mask is the leftmost element
    // so that it's processed together with null partial renaming
    (prun.reverse, ty.force) match
      case (Mask.Pruned :: rem, Val.Pi(param, ty, cl, icit)) =>
        // skip let-defined variable and skip the renaming
        go(rem, pren.skip, cl(pren.nextCod))
      case (Mask.Keep(_) :: rem, Val.Pi(param, ty, cl, icit)) =>
        // lift for bound variable and do the renaming
        val next = go(rem, pren.lift, cl(pren.nextCod))
        // first variable is the leftmost param of Pi chain
        Term.Pi(param, rename(pren, ty), next, icit)
      case (Nil, ty) =>
        // starting point of term construction
        rename(pren, ty)
      case _ => throw InnerError.PruningUnknownError()
  // start with null renaming, coincides with the intuition that
  // in null context Pi always starts with (_ : U) -> ...
  go(prun, PartialRenaming(0, 0, Map(), None), ty)

// a non-tail-recursive implementation, but less readable
// benchmark result is 25% better than the tail-recursive one
def pruneTy2(prun: Pruning, ty: Val): Term =
  val (pr, remTy, tmMaker) = prun
    .foldRight((PartialRenaming(0, 0, Map(), None), ty, identity[Term]))(
      (mask, pair) =>
        val (pr, ty, tmMaker) = pair
        ty.force match
          case Val.Pi(param, ty, cl, icit) =>
            mask match
              case Mask.Pruned =>
                (pr.skip, cl(pr.nextCod), tmMaker)
              case Mask.Keep(_) =>
                // map later variables to the right of Pi chain
                def f(tm: Term) =
                  tmMaker(Term.Pi(param, rename(pr, ty), tm, icit))
                (pr.lift, cl(pr.nextCod), f)
          case _ => throw InnerError.PruningUnknownError()
    )
  // renamed remTy will be sent to Pi chain's return type
  tmMaker(rename(pr, remTy))

// prune the type of a meta and generate a new equation
// for example to prune `A` from `?0 : A -> B -> C`,
// we get `?1 : B -> C` and `?0 = \a b. ?1 b`, returns `?1`
def pruneMeta(prun: Pruning, metaID: MetaID): Term =
  Meta.state(metaID) match
    case MetaState.Unsolved(ty) =>
      val prunedTy = eval(List(), pruneTy2(prun, ty))
      val newMeta = Term.Meta(Meta.create(prunedTy))
      // helper function to restore the original lambda structure
      def lams(ty: Val, lvl: Level): Term =
        if lvl == prun.length then Term.Inserted(newMeta, prun)
        else
          ty.force match
            case Val.Pi(param, ty, cl, icit) =>
              val newName = if param == "_" then "x" + lvl else param
              Term.Lam(newName, lams(cl(Val.Var(lvl)), lvl + 1), icit)
            case _ => throw InnerError.PruningUnknownError()
      // `ty` is used instead of `prunedTy` to sustain param count
      val boxed = lams(ty, 0)
      Meta.solve(metaID, eval(List(), boxed), ty)
      newMeta
    case MetaState.Solved(value, ty) =>
      throw InnerError.DuplicatedSolve("pruneMeta")

// state machine for pruneVFlex
enum PruneVFlexState:
  case OKRenaming
  case OKNonRenaming
  case NeedsPruning

  // transfer function of the state machine
  def transDef: PruneVFlexState = this match
    case NeedsPruning => throw InnerError.PruneNonRenaming()
    case _            => OKNonRenaming
  def transPrun: PruneVFlexState = this match
    case OKNonRenaming => throw InnerError.PruneNonRenaming()
    case _             => NeedsPruning

// prune a Val.Flex, which is a meta applied to a spine
// prunes meta type and spine at the same time
// for example to prune B from ?0 : A -> B -> X -> Y, ?0 a b x,
// we get ?1 : A -> X -> Y, ?0 = \a b. ?1 a, returns ?1 a x
// a haskell-ish implementation which is again very similar to the original
def pruneVFlex(pren: PartialRenaming, metaID: MetaID, spine: Spine): Term =
  Meta.state(metaID) match
    case MetaState.Unsolved(ty) =>
      val (filtSp, state) = spine.foldRight(
        (List[(Option[Term], Icit)](), PruneVFlexState.OKRenaming)
      )((param, pair) =>
        val (filtSp, state) = pair
        param.value.force match
          case Val.Rigid(level, List()) =>
            pren.map.get(level) match
              // prune variable
              case None => ((None, param.icit) :: filtSp, state.transPrun)
              // keep variable
              case Some(lvl) =>
                val x = (Some(pren.getTermDirect(lvl)), param.icit)
                (x :: filtSp, state)
          // not a renaming, is likely defined variable
          // or later-applied argument
          case value =>
            (
              (Some(rename(pren, value)), param.icit) :: filtSp,
              state.transDef
            )
      )
      // prune meta if needed
      val newMeta = state match
        case PruneVFlexState.NeedsPruning =>
          val prun = filtSp.map {
            case (None, _)    => Mask.Pruned
            case (Some(_), i) => Mask.Keep(i)
          }
          pruneMeta(prun, metaID)
        case _ => Term.Meta(metaID)
      // reapply pruned spine to meta
      filtSp.foldRight(newMeta)((pair, tm) =>
        val (opt, icit) = pair
        opt match
          case None        => tm
          case Some(value) => Term.App(tm, value, icit)
      )
    case MetaState.Solved(value, ty) =>
      throw InnerError.DuplicatedSolve("pruneVFlex")

// An more readable implementation utilizing mutable variables
def pruneVFlex2(pren: PartialRenaming, metaID: MetaID, spine: Spine): Term =
  Meta.state(metaID) match
    case MetaState.Unsolved(ty) =>
      var isRenaming = true
      var inScope = true
      val filtSp = spine.map { param =>
        param.value.force match
          case Val.Rigid(level, List()) =>
            pren.map.get(level) match
              // flag out-of-scope variable
              case None => inScope = false; (None, param.icit)
              // in-scope variable
              case Some(lvl) => (Some(pren.getTermDirect(lvl)), param.icit)
          case value =>
            // spine is not a renaming
            isRenaming = false
            (Some(rename(pren, value)), param.icit)
      }
      // only prune renaming
      if !isRenaming && !inScope then throw InnerError.PruneNonRenaming()
      // prune meta if needed
      val newMeta =
        if inScope then Term.Meta(metaID)
        else
          val prun = filtSp.map {
            case (None, _)    => Mask.Pruned
            case (Some(_), i) => Mask.Keep(i)
          }
          pruneMeta(prun, metaID)
      // reapply pruned spine to meta
      filtSp.foldRight(newMeta)((pair, tm) =>
        val (opt, icit) = pair
        opt match
          case None        => tm
          case Some(value) => Term.App(tm, value, icit)
      )
    case MetaState.Solved(value, ty) =>
      throw InnerError.DuplicatedSolve("pruneVFlex")

def invert(envLen: Level, spine: Spine): PartialRenaming =
  spine.foldRight(PartialRenaming(envLen, 0, Map(), None))((param, pr) =>
    param.value.force match
      case Val.Rigid(level, List()) =>
        PartialRenaming(pr.cod, pr.dom + 1, pr.map + (level -> pr.dom), pr.occ)
      case _ =>
        PartialRenaming(pr.cod, pr.dom + 1, pr.map, pr.occ)
  )

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
      else pruneVFlex2(pr, rhs, spine)
    case Val.Rigid(level, spine) =>
      renameSp(spine, pr.getTerm(level))
    case Val.Lam(param, cl, i) =>
      Term.Lam(param, rename(pr.lift, cl(pr.nextCod)), i)
    case Val.Pi(param, ty, cl, i) =>
      Term.Pi(param, rename(pr, ty), rename(pr.lift, cl(pr.nextCod)), i)

def solve(lhs: MetaID, envLen: Level, sp: Spine, rhs: Val): Unit =
  Meta.state(lhs) match
    case MetaState.Unsolved(ty) =>
      val pr = invert(envLen, sp).withOcc(lhs)
      val tm = rename(pr, rhs)
      val boxed = sp
        .foldLeft((tm, 0))((pair, param) =>
          val (term, lvl) = pair
          (Term.Lam("x" + lvl, term, param.icit), lvl + 1)
        )
        ._1
      Meta.solve(lhs, eval(List(), boxed), ty)
    case MetaState.Solved(_, _) => throw InnerError.DuplicatedSolve("solve")

def unify(envLen: Level, x: Val, y: Val): Unit =
  def unifySp(spx: Spine, spy: Spine) =
    if spx.length != spy.length then throw InnerError.SpineMismatch()
    spx.zip(spy).map((lhs, rhs) => unify(envLen, lhs.value, rhs.value))
  (x.force, y.force) match
    case (Val.U, Val.U) =>
    case (Val.Flex(x, spx), Val.Flex(y, spy)) if x == y =>
      unifySp(spx, spy)
    case (Val.Rigid(x, spx), Val.Rigid(y, spy)) if x == y =>
      unifySp(spx, spy)
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
