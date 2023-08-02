package `implicit`.fc

type Types = List[Val]
type Bindings = List[Binding]

enum Binding:
  case Bound
  case Defined

object Env:
  def filter(env: Env, bd: Bindings) =
    env.zip(bd).filter((v, b) => b == Binding.Bound).map(_._1)

case class Ctx(
    env: Env,
    types: Types,
    bindings: Bindings,
    nameMap: Map[Name, Level]
):
  def getVal(name: Name): Val = getVal(nameMap(name))
  def getVal(level: Level): Val = env(envLen - level - 1)
  def getType(name: Name): Val = getType(nameMap(name))
  def getType(level: Level): Val = types(envLen - level - 1)
  def getLevel(name: Name): Level = nameMap(name)
  def bind(name: Name, value: Val, ty: Val): Ctx =
    Ctx(
      value :: env,
      ty :: types,
      Binding.Bound :: bindings,
      nameMap + (name -> env.length)
    )
  def bind(name: Name, ty: Val): Ctx =
    bind(name, Val.Var(env.length), ty)
  def define(name: Name, value: Val, ty: Val): Ctx =
    Ctx(
      value :: env,
      ty :: types,
      Binding.Defined :: bindings,
      nameMap + (name -> env.length)
    )
  def define(name: Name, ty: Val): Ctx =
    define(name, Val.Var(env.length), ty)
  def envLen: Int = env.length
  def nextVal: Val = Val.Var(env.length)

object Ctx:
  def empty: Ctx = Ctx(List(), List(), List(), Map())
