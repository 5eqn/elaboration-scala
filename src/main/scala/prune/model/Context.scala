package prune.model

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
    names: Names,
    nameMap: Map[Name, (Level, Val)]
):
  def apply(name: Name): (Level, Val) =
    try nameMap(name)
    catch
      case _ =>
        throw new InnerError.NameNotFound(name)

  // there're lots of `Ctx` creator,
  // it's necessary to stop repeating myself
  def add(
      name: Name,
      value: Val,
      bd: Binding,
      ty: Val,
      inserted: Boolean
  ): Ctx =
    Ctx(
      value :: env,
      bd :: bindings,
      name :: names,
      // just don't add the variable to nameMap if it's inserted
      // because it's only used when inferring type of Raw.Var
      // you don't want `f : {A} -> A -> U = \x. A` to pass typecheck
      if inserted then nameMap else nameMap + (name -> (env.length, ty))
    )
  def define(name: Name, value: Val, ty: Val): Ctx =
    add(name, value, Binding.Defined, ty, false)
  def define(name: Name, ty: Val): Ctx =
    define(name, Val.Var(env.length), ty)
  def bind(name: Name, value: Val, ty: Val): Ctx =
    add(name, value, Binding.Bound, ty, false)
  def bind(name: Name, ty: Val): Ctx =
    bind(name, Val.Var(env.length), ty)
  def insert(name: Name, value: Val, ty: Val): Ctx =
    add(name, value, Binding.Bound, ty, true)
  def insert(name: Name, ty: Val): Ctx =
    insert(name, Val.Var(env.length), ty)
  def envLen: Int = env.length
  def nextVal: Val = Val.Var(env.length)

object Ctx:
  def empty: Ctx = Ctx(List(), List(), List(), Map())
