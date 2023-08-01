package exception.fc

case class PartialRenaming(cod: Level, dom: Level, map: Map[Int, Level]):
  def lift: PartialRenaming =
    PartialRenaming(cod + 1, dom + 1, map + (cod -> dom))
  def nextCod: Val = Val.Var(cod)

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
      if rhs == lhs then throw new Exception(s"$rhs occurs in rhs")
      else renameSp(spine, Term.Meta(rhs))
    case Val.Rigid(level, spine) =>
      renameSp(spine, Term.Var(pr.dom - pr.map(level) - 1))
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
  val unifySp = (x: Spine, y: Spine) =>
    x.foldLeft(y)((y, vx) =>
      y match
        case vy :: rem => unify(envLen, vx.value, vy.value); rem
        case _         => throw new Exception("spine length differs")
    )
  (x.force, y.force) match
    case (Val.U, Val.U) =>
    case (Val.Flex(x, spx), Val.Flex(y, spy)) if x == y =>
      unifySp(spx, spy)
    case (Val.Rigid(x, spx), Val.Rigid(y, spy)) if x == y =>
      unifySp(spx, spy)
    case (Val.Flex(id, spine), y) => solve(id, envLen, spine, y)
    case (x, Val.Flex(id, spine)) => solve(id, envLen, spine, x)
    case (Val.Lam(_, cl, i), y) =>
      val value = Val.Var(envLen)
      unify(envLen + 1, cl(value), y(Param(value, i)))
    case (x, Val.Lam(_, cl, i)) =>
      val value = Val.Var(envLen)
      unify(envLen + 1, x(Param(value, i)), cl(value))
    case (Val.Pi(_, ty1, cl1, i1), Val.Pi(_, ty2, cl2, i2)) =>
      if i1 != i2 then throw new Exception(s"icit differs: $i1 != $i2")
      val value = Val.Var(envLen)
      unify(envLen, ty1, ty2)
      unify(
        envLen + 1,
        cl1(value),
        cl2(value)
      )
    case _ => throw new Exception(s"unable to unify $x and $y")
