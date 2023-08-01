package exception.`catch`

enum Error extends Exception:

  // contextless errors
  case InferNamedLambda()
  case IntersectionRename()
  case ImplicitArgNotFound(name: Name)
  case IcitMismatch(fn: Icit, arg: Icit)

  // context inherit errors
  case ApplyToType(fn: Val, arg: Param)
  case ApplyWrongIcit(fn: Val, arg: Param, fnIcit: Icit)

  // contextful errors
  case InsertError(ctx: Ctx, tm: Term, ty: Val, next: Throwable)
  case UnifyError(ctx: Ctx, lhs: Val, rhs: Val, next: Throwable)
  case CheckError(ctx: Ctx, tm: Raw, ty: Term, next: Throwable)
  case InferError(ctx: Ctx, tm: Raw, next: Throwable)

  override def getMessage(): String = this match
    case InferNamedLambda() =>
      "Can't infer type of named lambda"
    case ApplyToType(fn, arg) =>
      "Can't apply argument to type"
    case ApplyWrongIcit(fn, arg, fnIcit) =>
      s"Can't apply argument with wrong icit to $fnIcit func"
    case IntersectionRename() =>
      "Intersection renaming is currently not supported"
    case ImplicitArgNotFound(name) =>
      s"Implicit argument $name not found"
    case IcitMismatch(fn, arg) =>
      s"Icit mismatch: function expects $fn, but argument is $arg"
    case InsertError(ctx, tm, ty, next) =>
      s"Can't insert '${tm.read(ctx)}' of type '$ty':\n\n${readError(next, ctx)}"
    case UnifyError(ctx, lhs, rhs, next) =>
      s"Can't unify '${quote(ctx.envLen, lhs).read(ctx)}' and '${quote(ctx.envLen, rhs)
          .read(ctx)}':\n\n${readError(next, ctx)}"
    case CheckError(ctx, tm, ty, next) =>
      s"At Line ${tm.pos.line} Column ${tm.pos.column}:\n${tm.pos.longString}\n" +
        s"Can't check '${tm}' against '${ty.read(ctx)}':\n\n${readError(next, ctx)}"
    case InferError(ctx, tm, next) =>
      s"At Line ${tm.pos.line} Column ${tm.pos.column}:\n${tm.pos.longString}\n" +
        s"Can't infer type of '${tm}':\n\n${readError(next, ctx)}"

  def read(ctx: Ctx): String = this match
    case ApplyToType(fn, arg) =>
      s"Can't apply argument '${quote(ctx.envLen, arg.value).read(
          ctx
        )}' to type '${quote(ctx.envLen, fn).read(ctx)}'"
    case ApplyWrongIcit(fn, arg, fnIcit) =>
      s"Can't apply argument '${quote(ctx.envLen, arg.value).read(
          ctx
        )}' (${arg.icit}) with wrong icit to '${quote(ctx.envLen, fn).read(ctx)}' ($fnIcit)"
    case _ => getMessage()

def readError(error: Throwable, ctx: Ctx): String =
  if error.isInstanceOf[Error]
  then error.asInstanceOf[Error].read(ctx)
  else error.getMessage()
