package exception.`catch`

type Types = List[Val]
type Names = List[Name]

case class Ctx(
    env: Env,
    types: Types,
    names: Names,
    nameMap: Map[Name, Level]
):
  def getVal(name: Name): Val = getVal(nameMap(name))
  def getVal(level: Level): Val = env(envLen - level - 1)
  def getType(name: Name): Val = getType(nameMap(name))
  def getType(level: Level): Val = types(envLen - level - 1)
  def getLevel(name: Name): Level = nameMap(name)
  def add(name: Name, value: Val, ty: Val): Ctx =
    Ctx(
      value :: env,
      ty :: types,
      name :: names,
      nameMap + (name -> env.length)
    )
  def add(name: Name, ty: Val): Ctx =
    add(name, Val.Var(env.length), ty)
  def envLen: Int = env.length
  def nextVal: Val = Val.Var(env.length)

object Ctx:
  def empty: Ctx = Ctx(List(), List(), List(), Map())
