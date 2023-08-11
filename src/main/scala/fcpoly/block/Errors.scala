package fcpoly.block

case class RootError(ctx: Ctx, tm: Raw, next: InnerError) extends Exception:
  override def getMessage(): String =
    s"At Line ${tm.pos.line} Column ${tm.pos.column}:\n${tm.pos.longString}\n" +
      s"When checking or inferring $tm:\n\n${next.read(ctx)}"

enum InnerError extends Exception:
  case SpineMismatch()
  case PlainUnifyError()
  case InferNamedLambda()
  case PruneNonRenaming()
  case InvertNonRenaming()
  case IntersectionRename()
  case PruningUnknownError()
  case MetaRenameOutOfBound()
  case NameNotFound(name: Name)
  case IndexNotFound(index: Index)
  case DuplicatedSolve(place: String)
  case ImplicitArgNotFound(name: Name)
  case IcitMismatch(lhs: Icit, rhs: Icit)
  case BadApplication(fn: Val, arg: Param)
  case InsertError(ctx: Ctx, tm: Term, next: InnerError)
  case UnifyError(ctx: Ctx, lhs: Val, rhs: Val, next: InnerError)

  def read(ctx: Ctx): String = this match
    case SpineMismatch() =>
      "Length of spine is different"
    case PlainUnifyError() =>
      "Values obviously inconsistent"
    case InferNamedLambda() =>
      "Can't infer type of named lambda"
    case PruneNonRenaming() =>
      "Can't prune a non-renaming spine"
    case IntersectionRename() =>
      "LHS meta appears in RHS, this is currently not supported"
    case PruningUnknownError() =>
      "Pruning failed for unknown reason"
    case InvertNonRenaming() =>
      "Can't invert a non-renaming spine"
    case MetaRenameOutOfBound() =>
      "Variable out of scope when solving meta"
    case NameNotFound(name) =>
      s"Name $name not found in context"
    case IndexNotFound(index) =>
      s"Index $index not found in environment"
    case DuplicatedSolve(place) =>
      s"Attempt to solve the same meta twice at $place"
    case ImplicitArgNotFound(name) =>
      s"Implicit argument $name not found"
    case IcitMismatch(lhs, rhs) =>
      s"Icit mismatch: lhs is $lhs, but rhs is $rhs"
    case BadApplication(fn, arg) =>
      s"Can't apply '${arg.read(ctx)}' to '${fn.read(ctx)}'"
    case InsertError(ctx, tm, next) =>
      s"Can't insert '${tm.read(ctx)}':\n\n${next.read(ctx)}"
    case UnifyError(ctx, lhs, rhs, next) =>
      s"Can't unify '${lhs.read(ctx)}' and '${rhs.read(ctx)}':\n\n${next.read(ctx)}"