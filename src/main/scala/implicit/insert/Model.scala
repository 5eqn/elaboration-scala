package `implicit`.insert

type Name = String
type Index = Int
type Level = Int
type Env = List[Val]
type Spine = List[Param]

object Spine:
  def apply(env: Env): Spine =
    env.map(value => Param(value, Icit.Expl))

case class Param(value: Val, icit: Icit):
  def force: Param = Param(value.force, icit)

enum Icit:
  case Expl
  case Impl

enum Dst:
  case Expl
  case ImplAuto
  case ImplBind(to: Name)

  def icit: Icit = this match
    case Expl        => Icit.Expl
    case ImplAuto    => Icit.Impl
    case ImplBind(_) => Icit.Impl

enum Src:
  case Expl
  case ImplAuto
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
