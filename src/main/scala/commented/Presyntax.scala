package commented

import scala.util.parsing.input.Positional
import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition

// Destination of application,
//
// Expl : explicit application, fn arg
// ImplAuto : implicit application based on position, fn {arg}
// ImplBind : implicit application based on name, fn {A = arg}
enum Dst:
  case Expl
  case ImplAuto
  case ImplBind(to: Name)

  def icit: Icit = this match
    case Expl        => Icit.Expl
    case ImplAuto    => Icit.Impl
    case ImplBind(_) => Icit.Impl

// Source of lambda,
//
// Expl : explicit lambda, \x.
// ImplAuto : implicit lambda based on position, \{x}.
// ImplBind : implicit lambda based on name, \{A = x}.
enum Src:
  case Expl
  case ImplAuto
  case ImplBind(from: Name)

  def icit: Icit = this match
    case Expl        => Icit.Expl
    case ImplAuto    => Icit.Impl
    case ImplBind(_) => Icit.Impl

// Raw syntax representation.
//
// U    | U
// Hole | _
// Var  | name
// App  | func arg
// Lam  | \(param : ty). body
// Pi   | (param : ty). body
// Let  | let name : ty = body; next
enum Raw extends Positional:
  case U
  case Hole
  case Var(name: Name)
  case App(func: Raw, arg: Raw, dst: Dst)
  case Lam(param: Name, ty: Option[Raw], body: Raw, src: Src)
  case Pi(param: Name, ty: Raw, body: Raw, icit: Icit)
  case Let(name: Name, ty: Raw, body: Raw, next: Raw)

  // make sure all Raw instances have position
  def ensurePosed(defPos: Position): Unit =
    this setPos defPos
    this match
      case App(func, arg, dst) =>
        func.ensurePosed(pos)
        arg.ensurePosed(pos)
      case Lam(param, ty, body, src) =>
        ty.map(_.ensurePosed(pos))
        body.ensurePosed(pos)
      case Pi(param, ty, body, icit) =>
        ty.ensurePosed(pos)
        body.ensurePosed(pos)
      case Let(name, ty, body, next) =>
        ty.ensurePosed(pos)
        body.ensurePosed(pos)
        next.ensurePosed(pos)
      case _ =>

  // pretty printing
  override def toString(): String = this match
    case U         => "U"
    case Hole      => "_"
    case Var(name) => name
    case App(func, arg, dst) =>
      dst match
        case Dst.Expl           => s"$func($arg)"
        case Dst.ImplAuto       => s"$func{$arg}"
        case Dst.ImplBind(name) => s"$func{$name = $arg}"
    case Lam(param, mTy, body, src) =>
      (src, mTy) match
        case (Src.Expl, None)               => s"λ$param. $body"
        case (Src.ImplAuto, None)           => s"λ{$param}. $body"
        case (Src.ImplBind(name), None)     => s"λ{$name = $param}. $body"
        case (Src.Expl, Some(ty))           => s"λ($param : $ty). $body"
        case (Src.ImplAuto, Some(ty))       => s"λ{$param : $ty}. $body"
        case (Src.ImplBind(name), Some(ty)) => s"λ{$name = $param : $ty}. $body"
    case Pi(param, ty, body, icit) =>
      icit.match
        case Icit.Expl => s"($param : $ty) -> ($body)"
        case Icit.Impl => s"{$param : $ty} -> ($body)"
    case Let(name, ty, body, next) => s"let $name : $ty = $body;\n$next"