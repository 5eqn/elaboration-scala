package commented

type Env = List[Val]

// Helper functions for environment of values.
object Env:
  def filter(env: Env, prun: Pruning) =
    env
      .zip(prun)
      .collect { case (v, Mask.Keep(i)) =>
        Param(v, i)
      }
  def get(env: Env, index: Index) =
    try env(index)
    catch case _ => throw InnerError.IndexNotFound(index)

type Spine = List[Param]

// A parameter with value and icit,
// fn (param) or fn {param}.
case class Param(value: Val, icit: Icit):
  def force: Param = Param(value.force, icit)
  def read(ctx: Ctx): String = icit match
    case Icit.Expl => value.read(ctx)
    case Icit.Impl => s"{${value.read(ctx)}}"

// A closure storing a term and its "partial environment",
// lacking the actual argument, this can simulate a
// `Val -> Val` effectively.
case class Closure(env: Env, body: Term):
  def apply(arg: Val): Val = eval(arg :: env, body)

// Representation of ground-level value.
//
// U     | U
// Flex  | ?metaID [spine]
// Rigid | Var(level) [spine]
// Lam   | \(param : ty). body
// Pi    | (param : ty). body
enum Val:
  case U
  case Flex(metaID: MetaID, spine: Spine)
  case Rigid(level: Level, spine: Spine)
  case Lam(param: Name, cl: Closure, icit: Icit)
  case Pi(param: Name, ty: Val, cl: Closure, icit: Icit)

  def read(ctx: Ctx): String = quote(ctx.envLen, this).read(ctx)

  def apply(u: Param): Val = this match
    case Lam(param, cl, _)   => cl(u.value)
    case Rigid(level, spine) => Rigid(level, u :: spine)
    case Flex(metaID, spine) => Flex(metaID, u :: spine)
    case _                   => throw InnerError.BadApplication(this, u)

  def apply(sp: Spine): Val =
    sp.foldRight(this)((value, term) => term(value))

  def force: Val = this match
    case Flex(metaID, spine) =>
      Meta.state(metaID) match
        case MetaState.Unsolved(_, _)   => this
        case MetaState.Solved(value, _) => value(spine).force
    case _ => this

// Helper functions for creating spineless values.
object Val:
  def Var(level: Level): Val = Rigid(level, List())
  def Meta(metaID: MetaID): Val = Flex(metaID, List())
