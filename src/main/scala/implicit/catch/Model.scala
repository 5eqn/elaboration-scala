package `implicit`.`catch`

import scala.util.parsing.input.Positional
import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition

type Types = List[Val]
type Names = List[Name]
type Bindings = List[Binding]

enum Binding:
  case Bound
  case Defined

object Env:
  def filter(env: Env, bd: Bindings) =
    env.zip(bd).filter((v, b) => b == Binding.Bound).map(_._1)

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

  // helper function for serializing param with icit
  def read(ctx: Ctx): String = icit match
    case Icit.Expl => value.read(ctx)
    case Icit.Impl => s"{${value.read(ctx)}}"

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

// make `Raw` extend `Positional` so that it has a `pos` field
enum Raw extends Positional:
  case U
  case Hole
  case Var(name: Name)
  case App(func: Raw, arg: Raw, dst: Dst)
  case Lam(param: Name, body: Raw, src: Src)
  case Pi(param: Name, ty: Raw, body: Raw, icit: Icit)
  case Let(name: Name, ty: Raw, body: Raw, next: Raw)

  // spread position data from root to leaves
  def ensurePosed(defPos: Position): Unit =
    this setPos defPos
    this match
      case App(func, arg, dst) =>
        func.ensurePosed(pos)
        arg.ensurePosed(pos)
      case Lam(param, body, src) =>
        body.ensurePosed(pos)
      case Pi(param, ty, body, icit) =>
        ty.ensurePosed(pos)
        body.ensurePosed(pos)
      case Let(name, ty, body, next) =>
        ty.ensurePosed(pos)
        body.ensurePosed(pos)
        next.ensurePosed(pos)
      case _ =>

  // a naive serialization of `Raw`
  override def toString(): String = this match
    case U         => "U"
    case Hole      => "_"
    case Var(name) => name
    case App(func, arg, dst) =>
      dst match
        case Dst.Expl           => s"$func($arg)"
        case Dst.ImplAuto       => s"$func{$arg}"
        case Dst.ImplBind(name) => s"$func{$name = $arg}"
    case Lam(param, body, src) =>
      src match
        case Src.Expl           => s"λ$param. $body"
        case Src.ImplAuto       => s"λ{$param}. $body"
        case Src.ImplBind(name) => s"λ{$name = $param}. $body"
    case Pi(param, ty, body, icit) =>
      icit.match
        case Icit.Expl => s"($param : $ty) -> ($body)"
        case Icit.Impl => s"{$param : $ty} -> ($body)"
    case Let(name, ty, body, next) => s"let $name : $ty = $body; $next"

enum Term:
  case U
  case Meta(metaID: MetaID)
  case Inserted(metaID: MetaID, bindings: Bindings)
  case Var(index: Index)
  case App(func: Term, arg: Term, icit: Icit)
  case Lam(param: Name, body: Term, icit: Icit)
  case Pi(param: Name, ty: Term, body: Term, icit: Icit)
  case Let(name: Name, ty: Term, body: Term, next: Term)

  // a naive serialization of `Term` utilizing the context
  def read(ctx: Ctx): String = this match
    case U                   => "U"
    case Meta(metaID)        => s"?$metaID"
    case Inserted(metaID, _) => "_"
    case Var(index)          => ctx.names(index)
    case App(func, arg, icit) =>
      icit match
        case Icit.Expl => s"${func.read(ctx)}(${arg.read(ctx)})"
        case Icit.Impl => s"${func.read(ctx)}{${arg.read(ctx)}}"
    case Lam(param, body, icit) =>
      icit match
        case Icit.Expl => s"λ$param. ${body.read(ctx.bind(param, Val.U))}"
        case Icit.Impl => s"λ{$param}. ${body.read(ctx.bind(param, Val.U))}"
    case Pi(param, ty, body, icit) =>
      icit match
        case Icit.Expl =>
          s"($param : ${ty.read(ctx)}) -> (${body.read(ctx.bind(param, Val.U))})"
        case Icit.Impl =>
          s"{$param : ${ty.read(ctx)}} -> (${body.read(ctx.bind(param, Val.U))})"
    case Let(name, ty, body, next) =>
      s"let $name : ${ty.read(ctx)} = ${body
          .read(ctx)}; ${next.read(ctx.bind(name, Val.U))}"

enum Val:
  case U
  case Flex(metaID: MetaID, spine: Spine)
  case Rigid(level: Level, spine: Spine)
  case Lam(param: Name, cl: Closure, icit: Icit)
  case Pi(param: Name, ty: Val, cl: Closure, icit: Icit)

  // serialization of `Val` utilizes `quote`
  def read(ctx: Ctx): String = quote(ctx.envLen, this).read(ctx)

  def apply(u: Param): Val = this match
    case Lam(param, cl, _)   => cl(u.value)
    case Rigid(level, spine) => Rigid(level, u :: spine)
    case Flex(metaID, spine) => Flex(metaID, u :: spine)
    case _                   => throw new InnerError.BadApplication(this, u)

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
