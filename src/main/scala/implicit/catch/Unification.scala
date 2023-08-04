package `implicit`.`catch`

case class PartialRenaming(cod: Level, dom: Level, map: Map[Level, Level]):
  def lift: PartialRenaming =
    PartialRenaming(cod + 1, dom + 1, map + (cod -> dom))
  def nextCod: Val = Val.Var(cod)

  // this map access should throw InnerError as well
  def getTerm(level: Level): Term =
    try Term.Var(dom - map(level) - 1)
    catch
      case _ =>
        throw InnerError.PruningRename()

def invert(envLen: Level, spine: Spine): PartialRenaming =
  spine.foldRight(PartialRenaming(envLen, 0, Map()))((param, pr) =>
    param.value.force match
      case Val.Rigid(level, List()) =>
        PartialRenaming(pr.cod, pr.dom + 1, pr.map + (level -> pr.dom))
      case _ =>
        PartialRenaming(pr.cod, pr.dom + 1, pr.map)
  )

def rename(lhs: MetaID, pr: PartialRenaming, value: Val): Term =
  val renameSp = (spine: Spine, initialTerm: Term) =>
    spine.foldRight(initialTerm)((param, term) =>
      Term.App(term, rename(lhs, pr, param.value), param.icit)
    )
  value.force match
    case Val.U =>
      Term.U
    case Val.Flex(rhs, spine) =>
      if rhs == lhs then throw InnerError.IntersectionRename()
      else renameSp(spine, Term.Meta(rhs))
    case Val.Rigid(level, spine) =>
      renameSp(spine, pr.getTerm(level))
    case Val.Lam(param, cl, i) =>
      Term.Lam(param, rename(lhs, pr.lift, cl(pr.nextCod)), i)
    case Val.Pi(param, ty, cl, i) =>
      Term.Pi(
        param,
        rename(lhs, pr, ty),
        rename(lhs, pr.lift, cl(pr.nextCod)),
        i
      )

def solve(lhs: MetaID, envLen: Level, sp: Spine, rhs: Val): Unit =
  val pr = invert(envLen, sp)
  val tm = rename(lhs, pr, rhs)
  Meta.solve(
    lhs,
    eval(
      List(),
      sp.foldLeft((tm, 0))((pair, param) =>
        val (term, lvl) = pair
        (Term.Lam("x" + lvl, term, param.icit), lvl + 1)
      )._1
    )
  )

def unify(envLen: Level, x: Val, y: Val): Unit =
  val unifySp = (spx: Spine, spy: Spine) =>
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

// use a catcher function to avoid passing `Ctx` in unify
def unifyCatch(ctx: Ctx, x: Val, y: Val): Unit =
  try unify(ctx.envLen, x, y)
  catch
    case e: InnerError =>
      throw InnerError.UnifyError(ctx, x, y, e)