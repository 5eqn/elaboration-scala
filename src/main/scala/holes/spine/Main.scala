package holes.spine

type Name = String
type Env = List[Val]
type Types = List[Val]
type Spine = List[Val]
type Index = Int
type Level = Int

// From `holes.assemble` to `holes.spine`,
// the only change is that `Val` features `Spine`.

case class Ctx(
    env: Env,
    types: Types,
    nameMap: Map[Name, Level]
):
  def getVal(name: Name): Val = getVal(nameMap(name))
  def getVal(level: Level): Val = env(envLen - level - 1)
  def getType(name: Name): Val = getType(nameMap(name))
  def getType(level: Level): Val = types(envLen - level - 1)
  def getLevel(name: Name): Level = nameMap(name)
  def add(name: Name, value: Val, ty: Val): Ctx =
    Ctx(value :: env, ty :: types, nameMap + (name -> env.length))
  def add(name: Name, ty: Val): Ctx =
    add(name, Val.Var(env.length), ty)
  def envLen: Int = env.length
  def nextVal: Val = Val.Var(env.length)

object Ctx {
  def empty: Ctx = Ctx(List(), List(), Map())
}

case class Closure(env: Env, body: Term):
  def apply(arg: Val): Val = eval(arg :: env, body)

enum Raw:
  case U
  case Var(name: Name)
  case App(func: Raw, arg: Raw)
  case Lam(param: Name, body: Raw)
  case Pi(param: Name, ty: Raw, body: Raw)
  case Let(name: Name, ty: Raw, body: Raw, next: Raw)

enum Term:
  case U
  case Var(index: Index)
  case App(func: Term, arg: Term)
  case Lam(param: Name, body: Term)
  case Pi(param: Name, ty: Term, body: Term)
  case Let(name: Name, ty: Term, body: Term, next: Term)

enum Val:
  case U
  case Rigid(level: Level, spine: Spine)
  case Lam(param: Name, cl: Closure)
  case Pi(param: Name, ty: Val, cl: Closure)

  def apply(u: Val): Val = this match
    case Lam(param, cl)      => cl(u)
    case Rigid(level, spine) => Rigid(level, u :: spine)
    case _                   => throw new Exception("impossible")

object Val {
  def Var(level: Level): Val = Rigid(level, List())
}

def eval(env: Env, tm: Term): Val = tm match
  case Term.U =>
    Val.U
  case Term.Var(index) =>
    env(index)
  case Term.App(func, arg) =>
    eval(env, func)(eval(env, arg))
  case Term.Lam(param, body) =>
    Val.Lam(param, Closure(env, body))
  case Term.Pi(param, ty, body) =>
    Val.Pi(param, eval(env, ty), Closure(env, body))
  case Term.Let(name, ty, body, next) =>
    eval(eval(env, body) :: env, next)

def quote(envLen: Int, x: Val): Term = x match
  case Val.U =>
    Term.U
  case Val.Rigid(level, spine) =>
    spine.foldRight(Term.Var(envLen - level - 1))((value, tm) =>
      Term.App(tm, quote(envLen, value))
    )
  case Val.Lam(param, cl) =>
    Term.Lam(param, quote(envLen + 1, cl(Val.Var(envLen))))
  case Val.Pi(param, ty, cl) =>
    Term.Pi(
      param,
      quote(envLen, ty),
      quote(envLen + 1, cl(Val.Var(envLen)))
    )

def conv(env: Env, x: Val, y: Val): Boolean = (x, y) match
  case (Val.U, Val.U) =>
    true
  case (Val.Rigid(x, spx), Val.Rigid(y, spy)) =>
    x == y && spx
      .foldRight((spy, true))((vx, pair) =>
        val (spy, res) = pair
        spy match
          case vy :: rem => (rem, res && conv(env, vx, vy))
          case _         => (List(), false)
      )
      ._2
  case (Val.Lam(_, cl), y) =>
    val value = Val.Var(env.length)
    conv(value :: env, cl(value), y(value))
  case (x, Val.Lam(_, cl)) =>
    val value = Val.Var(env.length)
    conv(value :: env, x(value), cl(value))
  case (Val.Pi(_, ty1, cl1), Val.Pi(_, ty2, cl2)) =>
    val value = Val.Var(env.length)
    conv(env, ty1, ty2) && conv(
      value :: env,
      cl1(value),
      cl2(value)
    )
  case _ =>
    false

def infer(ctx: Ctx, tm: Raw): (Term, Val) = tm match
  case Raw.U =>
    (Term.U, Val.U)
  case Raw.Var(name) =>
    (Term.Var(ctx.envLen - ctx.getLevel(name) - 1), ctx.getType(name))
  case Raw.App(func, arg) =>
    infer(ctx, func) match
      case (funcTerm, Val.Pi(_, ty, cl)) =>
        val argTerm = check(ctx, arg, ty)
        (Term.App(funcTerm, argTerm), cl(eval(ctx.env, argTerm)))
      case _ =>
        throw new Exception(s"$func is not a function")
  case Raw.Lam(param, body) =>
    throw new Exception(s"type of \\$param => $body can't be inferred")
  case Raw.Pi(param, ty, body) =>
    val tyTerm = check(ctx, ty, Val.U)
    val tyVal = eval(ctx.env, tyTerm)
    val bodyTerm = check(ctx.add(param, tyVal), body, Val.U)
    (Term.Pi(param, tyTerm, bodyTerm), Val.U)
  case Raw.Let(name, ty, body, next) =>
    val tyTerm = check(ctx, ty, Val.U)
    val tyVal = eval(ctx.env, tyTerm)
    val bodyTerm = check(ctx, body, tyVal)
    val bodyVal = eval(ctx.env, bodyTerm)
    val (nextTerm, nextTy) = infer(ctx.add(name, bodyVal, tyVal), next)
    (Term.Let(name, tyTerm, bodyTerm, nextTerm), nextTy)

def check(ctx: Ctx, tm: Raw, ty: Val): Term = (tm, ty) match
  case (Raw.Lam(param, body), Val.Pi(_, ty, cl)) =>
    val value = ctx.nextVal
    val bodyVal = check(ctx.add(param, value, ty), body, cl(value))
    Term.Lam(param, bodyVal)
  case _ =>
    val (term, value) = infer(ctx, tm)
    if conv(ctx.env, value, ty) then term
    else
      throw new Exception(
        s"$term has type $value but $ty was expected\nctx: $ctx"
      )
