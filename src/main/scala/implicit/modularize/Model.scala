package `implicit`.modularize

type Name = String
type Index = Int
type Level = Int
type Env = List[Val]
type Spine = List[Val]

enum Raw:
  case U
  case Hole
  case Var(name: Name)
  case App(func: Raw, arg: Raw)
  case Lam(param: Name, body: Raw)
  case Pi(param: Name, ty: Raw, body: Raw)
  case Let(name: Name, ty: Raw, body: Raw, next: Raw)

enum Term:
  case U
  case Meta(metaID: MetaID)
  case Inserted(metaID: MetaID, bindings: Bindings)
  case Var(index: Index)
  case App(func: Term, arg: Term)
  case Lam(param: Name, body: Term)
  case Pi(param: Name, ty: Term, body: Term)
  case Let(name: Name, ty: Term, body: Term, next: Term)

enum Val:
  case U
  case Flex(metaID: MetaID, spine: Spine)
  case Rigid(level: Level, spine: Spine)
  case Lam(param: Name, cl: Closure)
  case Pi(param: Name, ty: Val, cl: Closure)

  def apply(u: Val): Val = this match
    case Lam(param, cl)      => cl(u)
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
