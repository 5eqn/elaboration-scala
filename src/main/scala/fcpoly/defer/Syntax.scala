package fcpoly.defer

enum Mask:
  case Keep(i: Icit)
  case Pruned

type Pruning = List[Mask]

def readPrun(ctx: Ctx): String = ctx.prun
  .zip(ctx.env)
  .reverse
  .map {
    case (Mask.Keep(Icit.Expl), value) => s" ${value.read(ctx)}"
    case (Mask.Keep(Icit.Impl), value) => s" {${value.read(ctx)}}"
    case (Mask.Pruned, _)              => ""
  }
  .mkString("")

enum Local:
  case Bind(name: Name, ty: Term)
  case Define(name: Name, ty: Term, tm: Term)

type Locals = List[Local]

object Locals:
  def toTerm(loc: Locals, initTy: Term): Term =
    loc.foldLeft(initTy)((term, local) =>
      local match
        case Local.Bind(name, ty)         => Term.Pi(name, ty, term, Icit.Expl)
        case Local.Define(name, ty, body) => Term.Let(name, ty, body, term)
    )
  def toLams(loc: Locals, initTm: Term): Term =
    loc.foldLeft(initTm)((term, local) =>
      local match
        case Local.Bind(name, ty)         => Term.Lam(name, term, Icit.Expl)
        case Local.Define(name, ty, body) => Term.Let(name, ty, body, term)
    )

enum Term:
  case U
  case Meta(metaID: MetaID)
  // representing an unchecked term,
  // really unchecked ones are placeholder,
  // checked ones are stored in Check.map
  case Unchecked(checkID: CheckID)
  case Inserted(func: Term, prun: Pruning)
  case Var(index: Index)
  case App(func: Term, arg: Term, icit: Icit)
  case Lam(param: Name, body: Term, icit: Icit)
  case Pi(param: Name, ty: Term, body: Term, icit: Icit)
  case Let(name: Name, ty: Term, body: Term, next: Term)

  def read(ctx: Ctx): String = this match
    case U            => "U"
    case Meta(metaID) => s"?$metaID"
    // serialization for unchecked variable
    case Unchecked(checkID) =>
      Check.state(checkID) match
        case CheckState.Unchecked(ctx, _, _, metaID) =>
          s"?$metaID" + readPrun(ctx)
        case CheckState.Checked(tm) => tm.read(ctx)
    case Inserted(func, prun) =>
      func.read(ctx) + readPrun(ctx)
    case Var(index) => ctx.names(index)
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
          .read(ctx)};\n${next.read(ctx.define(name, Val.U, Val.U, Term.U, Term.U))}"
