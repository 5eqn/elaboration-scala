package `implicit`.modularize

case class PartialRenaming(cod: Level, dom: Level, map: Map[Int, Level]):
  def lift: PartialRenaming =
    PartialRenaming(cod + 1, dom + 1, map + (cod -> dom))
  def nextCod: Val = Val.Var(cod)

def invert(envLen: Level, spine: Spine): PartialRenaming =
  spine.foldRight(PartialRenaming(envLen, 0, Map()))((value, pr) =>
    value.force match
      case Val.Rigid(level, List()) =>
        PartialRenaming(pr.cod, pr.dom + 1, pr.map + (level -> pr.dom))
      case _ =>
        throw new Exception("can't invert non-renaming spine")
  )

def rename(lhs: MetaID, pr: PartialRenaming, value: Val): Term =
  val renameSp = (spine: Spine, initialTerm: Term) =>
    spine.foldRight(initialTerm)((value, term) =>
      Term.App(term, rename(lhs, pr, value))
    )
  value.force match
    case Val.U =>
      Term.U
    case Val.Flex(rhs, spine) =>
      if rhs == lhs then throw new Exception(s"$rhs occurs in rhs")
      else renameSp(spine, Term.Meta(rhs))
    case Val.Rigid(level, spine) =>
      renameSp(spine, Term.Var(pr.dom - pr.map(level) - 1))
    case Val.Lam(param, cl) =>
      Term.Lam(param, rename(lhs, pr.lift, cl(pr.nextCod)))
    case Val.Pi(param, ty, cl) =>
      Term.Pi(
        param,
        rename(lhs, pr, ty),
        rename(lhs, pr.lift, cl(pr.nextCod))
      )

def solve(lhs: MetaID, envLen: Level, sp: Spine, rhs: Val): Unit =
  val pr = invert(envLen, sp)
  val tm = rename(lhs, pr, rhs)
  Meta.solve(
    lhs,
    eval(
      List(),
      (0 until pr.dom).foldRight(tm)((lvl, term) => Term.Lam("x" + lvl, term))
    )
  )

def unify(envLen: Level, x: Val, y: Val): Unit =
  val unifySp = (x: Spine, y: Spine) =>
    if x.length != y.length then throw new Exception("spine length mismatch")
    x.zip(y).map((lhs, rhs) => unify(envLen, lhs, rhs))
  (x.force, y.force) match
    case (Val.U, Val.U) =>
    case (Val.Flex(x, spx), Val.Flex(y, spy)) if x == y =>
      unifySp(spx, spy)
    case (Val.Rigid(x, spx), Val.Rigid(y, spy)) if x == y =>
      unifySp(spx, spy)
    case (Val.Flex(id, spine), y) => solve(id, envLen, spine, y)
    case (x, Val.Flex(id, spine)) => solve(id, envLen, spine, x)
    case (Val.Lam(_, cl), y) =>
      val value = Val.Var(envLen)
      unify(envLen + 1, cl(value), y(value))
    case (x, Val.Lam(_, cl)) =>
      val value = Val.Var(envLen)
      unify(envLen + 1, x(value), cl(value))
    case (Val.Pi(_, ty1, cl1), Val.Pi(_, ty2, cl2)) =>
      val value = Val.Var(envLen)
      unify(envLen, ty1, ty2)
      unify(
        envLen + 1,
        cl1(value),
        cl2(value)
      )
    case _ => throw new Exception(s"unable to unify $x and $y")
