package `implicit`.model

type Name = String
type Index = Int
type Level = Int
type Env = List[Val]
type Spine = List[Param]

object Spine:
  // function that converts env to spine
  // now spine consists of `Param`s with explicit or implicit tag
  def apply(env: Env): Spine =
    env.map(value => Param(value, Icit.Expl))

case class Param(value: Val, icit: Icit):
  // force the value of param
  def force: Param = Param(value.force, icit)

enum Icit:
  case Expl
  case Impl

enum Dst:
  // explicit application, f A
  case Expl
  // implicit position-based application, f {A}
  case ImplAuto
  // implicit name-base application f {Ty = A}
  case ImplBind(to: Name)

  def icit: Icit = this match
    case Expl        => Icit.Expl
    case ImplAuto    => Icit.Impl
    case ImplBind(_) => Icit.Impl

enum Src:
  // explicit lambda, \x. x
  case Expl
  // implicit lambda with consistent names, \{x}. x
  case ImplAuto
  // implicit lambda with renaming, \{x = y}. y
  case ImplBind(from: Name)

  def icit: Icit = this match
    case Expl        => Icit.Expl
    case ImplAuto    => Icit.Impl
    case ImplBind(_) => Icit.Impl

enum Raw:
  case U
  case Hole
  case Var(name: Name)
  case App(func: Raw, arg: Raw, dst: Dst)
  case Lam(param: Name, body: Raw, src: Src)
  case Pi(param: Name, ty: Raw, body: Raw, icit: Icit)
  case Let(name: Name, ty: Raw, body: Raw, next: Raw)

enum Term:
  case U
  case Meta(metaID: MetaID)
  case Inserted(metaID: MetaID)
  case Var(index: Index)
  case App(func: Term, arg: Term, icit: Icit)
  case Lam(param: Name, body: Term, icit: Icit)
  case Pi(param: Name, ty: Term, body: Term, icit: Icit)
  case Let(name: Name, ty: Term, body: Term, next: Term)

enum Val:
  case U
  case Flex(metaID: MetaID, spine: Spine)
  case Rigid(level: Level, spine: Spine)
  case Lam(param: Name, cl: Closure, icit: Icit)
  case Pi(param: Name, ty: Val, cl: Closure, icit: Icit)

  def apply(u: Param): Val = this match
    // the icit is already checked, there's no need to check again
    case Lam(param, cl, _)   => cl(u.value)
    case Rigid(level, spine) => Rigid(level, u :: spine)
    case Flex(metaID, spine) => Flex(metaID, u :: spine)
    case _                   => throw new Exception("impossible")

  def apply(sp: Spine): Val =
    sp.foldRight(this)((value, term) => term(value))

  def force: Val = this match
    case Flex(metaID, spine) => Meta.value(metaID)(spine)
    case _                   => this

object Val:
  def Var(level: Level): Val = Rigid(level, List())
  def Meta(metaID: MetaID): Val = Flex(metaID, List())

case class Closure(env: Env, body: Term):
  def apply(arg: Val): Val = eval(arg :: env, body)
