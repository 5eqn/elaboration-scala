package `implicit`.`catch`

type Types = List[Val]
type Names = List[Name]
type Bindings = List[Binding]

enum Binding:
  case Bound
  case Defined

object Env:
  def filter(env: Env, bd: Bindings) =
    env.zip(bd).filter((v, b) => b == Binding.Bound).map(_._1)

case class Ctx(
    env: Env,
    bindings: Bindings,
    // a name list is added for reverse name finding
    names: Names,
    nameMap: Map[Name, (Level, Val)]
):
  // add error catching when accessing `nameMap` (the former `src`)
  def apply(name: Name): (Level, Val) =
    try nameMap(name)
    catch
      case _ =>
        throw new InnerError.NameNotFound(name)
  def define(name: Name, value: Val, ty: Val): Ctx =
    Ctx(
      value :: env,
      Binding.Defined :: bindings,
      name :: names,
      nameMap + (name -> (env.length, ty))
    )
  def define(name: Name, ty: Val): Ctx =
    define(name, Val.Var(env.length), ty)
  def bind(name: Name, value: Val, ty: Val): Ctx =
    Ctx(
      value :: env,
      Binding.Bound :: bindings,
      name :: names,
      nameMap + (name -> (env.length, ty))
    )
  def bind(name: Name, ty: Val): Ctx =
    bind(name, Val.Var(env.length), ty)
  def envLen: Int = env.length
  def nextVal: Val = Val.Var(env.length)

object Ctx:
  def empty: Ctx = Ctx(List(), List(), List(), Map())
