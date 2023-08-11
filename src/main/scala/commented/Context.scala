package commented

// Context for typecheck.
//
// `env` is used in evaluation to store "level -> value"
// `prun` is used as mask on `env` to get value of metas
// `locals` is used as type map to get type of metas
// `names` is used in pretty printing to store "level -> name"
// `nameMap` is used for inferring type of `Raw`
case class Ctx(
    env: Env,
    prun: Pruning,
    locals: Locals,
    names: Names,
    nameMap: Map[Name, (Level, Val)]
):
  // get level and type of a name
  def apply(name: Name): (Level, Val) =
    try nameMap(name)
    catch
      case _ =>
        throw InnerError.NameNotFound(name)

  // add a record to context
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

  // let-define a variable
  def define(name: Name, value: Val, ty: Val, vtm: Term, ttm: Term): Ctx =
    add(name, value, Mask.Pruned, Local.Define(name, ttm, vtm), ty, false)

  // bind a variable (pi / lambda)
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

  // insert a implicit lambda
  def insert(name: Name, value: Val, ty: Val): Ctx =
    add(
      name,
      value,
      // in `\{A} -> ?0 A`, argument `A` of `?0` is explicit
      Mask.Keep(Icit.Expl),
      Local.Bind(name, quote(envLen, ty)),
      ty,
      true
    )
  def insert(name: Name, ty: Val): Ctx =
    insert(name, Val.Var(env.length), ty)

  // get length of environment, representing how many variables are in context
  def envLen: Level = env.length

  // value of the next binder
  def nextVal: Val = Val.Var(env.length)

// Companion object for context, used for creating empty context intuitively
object Ctx:
  def empty: Ctx = Ctx(List(), List(), List(), List(), Map())
