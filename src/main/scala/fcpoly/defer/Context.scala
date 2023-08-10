package fcpoly.defer

case class Ctx(
    env: Env,
    prun: Pruning,
    locals: Locals,
    names: Names,
    nameMap: Map[Name, (Level, Val)]
):
  def apply(name: Name): (Level, Val) =
    try nameMap(name)
    catch
      case _ =>
        throw InnerError.NameNotFound(name)
  def add(
      name: Name,
      value: Val,
      mask: Mask,
      loc: Local,
      ty: Val,
      inserted: Boolean
  ): Ctx =
    Ctx(
      value :: env,
      mask :: prun,
      loc :: locals,
      name :: names,
      if inserted then nameMap else nameMap + (name -> (env.length, ty))
    )
  def define(name: Name, value: Val, ty: Val, vtm: Term, ttm: Term): Ctx =
    add(name, value, Mask.Pruned, Local.Define(name, ttm, vtm), ty, false)
  def bind(name: Name, value: Val, ty: Val): Ctx =
    add(
      name,
      value,
      Mask.Keep(Icit.Expl),
      Local.Bind(name, quote(envLen, ty)),
      ty,
      false
    )
  def bind(name: Name, ty: Val): Ctx =
    bind(name, Val.Var(env.length), ty)
  def insert(name: Name, value: Val, ty: Val): Ctx =
    add(
      name,
      value,
      Mask.Keep(Icit.Expl),
      Local.Bind(name, quote(envLen, ty)),
      ty,
      true
    )
  def insert(name: Name, ty: Val): Ctx =
    insert(name, Val.Var(env.length), ty)
  def envLen: Level = env.length
  def nextVal: Val = Val.Var(env.length)

object Ctx:
  def empty: Ctx = Ctx(List(), List(), List(), List(), Map())