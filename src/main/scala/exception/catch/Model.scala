package exception.`catch`

import scala.util.parsing.input.Positional

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

// extending `Positional` instantly adds `pos` field to `Raw`
enum Raw extends Positional:
  case U
  case Hole
  case Var(name: Name)
  case App(func: Raw, arg: Raw, dst: Dst)
  case Lam(param: Name, body: Raw, src: Src)
  case Pi(param: Name, ty: Raw, body: Raw, icit: Icit)
  case Let(name: Name, ty: Raw, body: Raw, next: Raw)

  override def toString(): String = this match
    case U         => "U"
    case Hole      => "_"
    case Var(name) => name
    case App(func, arg, dst) =>
      dst.icit match
        case Icit.Expl => s"${func}(${arg})"
        case Icit.Impl => s"${func}{${arg}}"
    case Lam(param, body, src) =>
      src.icit match
        case Icit.Expl => s"λ$param. ${body}"
        case Icit.Impl => s"λ{$param}. ${body}"
    case Pi(param, ty, body, icit) =>
      icit.match
        case Icit.Expl => s"($param : ${ty}) -> (${body})"
        case Icit.Impl => s"{$param : ${ty}} -> (${body})"
    case Let(name, ty, body, next) => s"let $name : ${ty} = ${body}; ${next}"

enum Term:
  case U
  case Meta(metaID: MetaID)
  case Inserted(metaID: MetaID)
  case Var(index: Index)
  case App(func: Term, arg: Term, icit: Icit)
  case Lam(param: Name, body: Term, icit: Icit)
  case Pi(param: Name, ty: Term, body: Term, icit: Icit)
  case Let(name: Name, ty: Term, body: Term, next: Term)

  def read(ctx: Ctx): String = this match
    case U                => "U"
    case Meta(metaID)     => s"?${metaID}"
    case Inserted(metaID) => "_"
    case Var(index)       => ctx.names(index)
    case App(func, arg, icit) =>
      icit match
        case Icit.Expl => s"${func.read(ctx)}(${arg.read(ctx)})"
        case Icit.Impl => s"${func.read(ctx)}{${arg.read(ctx)}}"
    case Lam(param, body, icit) =>
      icit match
        case Icit.Expl => s"λ$param. ${body.read(ctx.add(param, Val.U))}"
        case Icit.Impl => s"λ{$param}. ${body.read(ctx.add(param, Val.U))}"
    case Pi(param, ty, body, icit) =>
      icit match
        case Icit.Expl =>
          s"($param : ${ty.read(ctx)}) -> (${body.read(ctx.add(param, Val.U))})"
        case Icit.Impl =>
          s"{$param : ${ty.read(ctx)}} -> (${body.read(ctx.add(param, Val.U))})"
    case Let(name, ty, body, next) =>
      s"let $name : ${ty.read(ctx)} = ${body
          .read(ctx)}; ${next.read(ctx.add(name, Val.U))}"

enum Val:
  case U
  case Flex(metaID: MetaID, spine: Spine)
  case Rigid(level: Level, spine: Spine)
  case Lam(param: Name, cl: Closure, icit: Icit)
  case Pi(param: Name, ty: Val, cl: Closure, icit: Icit)

  def apply(u: Param): Val = this match
    case Lam(param, cl, i) =>
      if u.icit != i then throw new Error.ApplyWrongIcit(this, u, i)
      else cl(u.value)
    case Rigid(level, spine) => Rigid(level, u :: spine)
    case Flex(metaID, spine) => Flex(metaID, u :: spine)
    case _                   => throw new Error.ApplyToType(this, u)

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
