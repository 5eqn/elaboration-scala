// de-Bruijn index is added.
package typecheck.closure.debruijn

type Name = String
type Env = List[Val]
type Cxt = Map[Name, (Level, Val)]
type Index = Int
type Level = Int

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
  case Var(level: Level)
  case App(func: Val, arg: Val)
  case Lam(param: Name, cl: Closure)
  case Pi(param: Name, ty: Val, cl: Closure)

  def apply(u: Val): Val = this match
    case Lam(param, cl) => cl(u)
    case t              => App(t, u)

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

def quote(envLen: Level, x: Val): Term = x match
  case Val.U =>
    Term.U
  case Val.Var(level) =>
    Term.Var(envLen - level - 1)
  case Val.App(func, arg) =>
    Term.App(quote(envLen, func), quote(envLen, arg))
  case Val.Lam(param, cl) =>
    Term.Lam(param, quote(envLen + 1, cl(Val.Var(envLen))))
  case Val.Pi(param, ty, cl) =>
    Term.Pi(
      param,
      quote(envLen, ty),
      quote(envLen + 1, cl(Val.Var(envLen)))
    )

def conv(envLen: Level, x: Val, y: Val): Boolean = (x, y) match
  case (Val.U, Val.U) =>
    true
  case (Val.Var(x), Val.Var(y)) =>
    x == y
  case (Val.App(x1, x2), Val.App(y1, y2)) =>
    conv(envLen, x1, y1) && conv(envLen, x2, y2)
  case (Val.Lam(_, cl), y) =>
    val value = Val.Var(envLen)
    conv(envLen + 1, cl(value), y(value))
  case (x, Val.Lam(_, cl)) =>
    val value = Val.Var(envLen)
    conv(envLen + 1, x(value), cl(value))
  case (Val.Pi(_, ty1, cl1), Val.Pi(_, ty2, cl2)) =>
    val value = Val.Var(envLen)
    conv(envLen, ty1, ty2) && conv(
      envLen + 1,
      cl1(value),
      cl2(value)
    )
  case _ =>
    false

def infer(env: Env, cxt: Cxt, tm: Raw): (Term, Val) = tm match
  case Raw.U =>
    (Term.U, Val.U)
  case Raw.Var(name) =>
    cxt.get(name) match
      case Some((level, ty)) => (Term.Var(env.length - level - 1), ty)
      case None => throw new Exception(s"$name is not in the context")
  case Raw.App(func, arg) =>
    infer(env, cxt, func) match
      case (funcTerm, Val.Pi(_, ty, cl)) =>
        val argTerm = check(env, cxt, arg, ty)
        (Term.App(funcTerm, argTerm), cl(eval(env, argTerm)))
      case _ =>
        throw new Exception(s"$func is not a function")
  case Raw.Lam(param, body) =>
    throw new Exception(s"type of \\$param => $body can't be inferred")
  case Raw.Pi(param, ty, body) =>
    val tyTerm = check(env, cxt, ty, Val.U)
    val level = env.length
    val newEnv = Val.Var(level) :: env
    val newCxt = cxt + (param -> (level, eval(env, tyTerm)))
    val bodyTerm = check(newEnv, newCxt, body, Val.U)
    (Term.Pi(param, tyTerm, bodyTerm), Val.U)
  case Raw.Let(name, ty, body, next) =>
    val tyTerm = check(env, cxt, ty, Val.U)
    val valTy = eval(env, tyTerm)
    val bodyTerm = check(env, cxt, body, valTy)
    val newEnv = eval(env, bodyTerm) :: env
    val newCxt = cxt + (name -> (env.length, valTy))
    val (nextTerm, nextTy) = infer(newEnv, newCxt, next)
    (Term.Let(name, tyTerm, bodyTerm, nextTerm), nextTy)

def check(env: Env, cxt: Cxt, tm: Raw, ty: Val): Term = (tm, ty) match
  case (Raw.Lam(param, body), Val.Pi(_, ty, cl)) =>
    val level = env.length
    val value = Val.Var(level)
    val newEnv = value :: env
    val newCxt = cxt + (param -> (level, ty))
    val bodyVal = check(newEnv, newCxt, body, cl(value))
    Term.Lam(param, bodyVal)
  case _ =>
    val (term, value) = infer(env, cxt, tm)
    if conv(env.length, value, ty) then term
    else
      throw new Exception(
        s"$term has type $value but $ty was expected\nenv: $env\ncxt: $cxt"
      )
