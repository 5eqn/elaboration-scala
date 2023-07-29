package typecheck.closure.names

type Name = String
type Env = Map[Name, Val]
type Cxt = Map[Name, Val]

case class Closure(param: Name, env: Env, body: Term):
  def apply(arg: Val): Val = eval(env + (param -> arg), body)

enum Term:
  case U
  case Var(name: Name)
  case App(func: Term, arg: Term)
  case Lam(param: Name, body: Term)
  case Pi(param: Name, ty: Term, body: Term)
  case Let(name: Name, ty: Term, body: Term, next: Term)

enum Val:
  case U
  case Var(name: Name)
  case App(func: Val, arg: Val)
  case Lam(cl: Closure)
  case Pi(cl: Closure, ty: Val)

  def apply(u: Val): Val = this match
    case Lam(cl) => cl(u)
    case t       => App(t, u)

def fresh(ns: List[Name], x: Name): Name = x match
  case "_"                 => "_"
  case _ if ns.contains(x) => fresh(ns, x + "'")
  case _                   => x

def eval(env: Env, tm: Term): Val = tm match
  case Term.U =>
    Val.U
  case Term.Var(name) =>
    env.get(name).get
  case Term.App(func, arg) =>
    eval(env, func)(eval(env, arg))
  case Term.Lam(param, body) =>
    Val.Lam(Closure(param, env, body))
  case Term.Pi(param, ty, body) =>
    Val.Pi(Closure(param, env, body), eval(env, ty))
  case Term.Let(name, ty, body, next) =>
    eval(env + (name -> eval(env, body)), next)

def quote(ns: List[Name], x: Val): Term = x match
  case Val.U =>
    Term.U
  case Val.Var(name) =>
    Term.Var(name)
  case Val.App(func, arg) =>
    Term.App(quote(ns, func), quote(ns, arg))
  case Val.Lam(cl) =>
    val name = fresh(ns, cl.param)
    Term.Lam(name, quote(name :: ns, cl(Val.Var(name))))
  case Val.Pi(cl, ty) =>
    val name = fresh(ns, cl.param)
    Term.Pi(name, quote(ns, ty), quote(name :: ns, cl(Val.Var(name))))

def conv(env: Env, x: Val, y: Val): Boolean = (x, y) match
  case (Val.U, Val.U) =>
    true
  case (Val.Var(x), Val.Var(y)) =>
    x == y
  case (Val.App(x1, x2), Val.App(y1, y2)) =>
    conv(env, x1, y1) && conv(env, x2, y2)
  case (Val.Lam(cl1), Val.Lam(cl2)) =>
    val name = fresh(env.keys.toList, cl1.param);
    val value = Val.Var(name)
    conv(env + (name -> value), cl1(value), cl2(value))
  case (Val.Lam(cl), y) =>
    val name = fresh(env.keys.toList, cl.param)
    val value = Val.Var(name)
    conv(env + (name -> value), cl(value), Val.App(y, value))
  case (x, Val.Lam(cl)) =>
    val name = fresh(env.keys.toList, cl.param)
    val value = Val.Var(name)
    conv(env + (name -> value), Val.App(x, value), cl(value))
  case (Val.Pi(cl1, ty1), Val.Pi(cl2, ty2)) =>
    val name = fresh(env.keys.toList, cl1.param)
    val value = Val.Var(name)
    conv(env, ty1, ty2) && conv(
      env + (name -> value),
      cl1(value),
      cl2(value)
    )
  case _ =>
    false

def infer(env: Env, cxt: Cxt, tm: Term): Val = tm match
  case Term.U =>
    Val.U
  case Term.Var(name) =>
    cxt.get(name) match
      case Some(ty) => ty
      case None     => throw new Exception(s"$name is not in the context")
  case Term.App(func, arg) =>
    infer(env, cxt, func) match
      case Val.Pi(cl, ty) =>
        if check(env, cxt, arg, ty) then cl(eval(env, arg))
        else throw new Exception(s"$arg is not of type $ty")
      case _ =>
        throw new Exception(s"$func is not a function")
  case Term.Lam(param, body) =>
    throw new Exception(s"type of \\$param => $body can't be inferred")
  case Term.Pi(param, ty, body) =>
    if check(env, cxt, ty, Val.U) then
      val newEnv = env + (param -> Val.Var(param))
      val newCxt = cxt + (param -> eval(env, ty))
      if check(newEnv, newCxt, body, Val.U) then Val.U
      else throw new Exception(s"$body is not a type")
    else throw new Exception(s"$ty is not a type")
  case Term.Let(name, ty, body, next) =>
    if check(env, cxt, ty, Val.U) then
      val valTy = eval(env, ty)
      if check(env, cxt, body, valTy) then
        val newEnv = env + (name -> eval(env, body))
        val newCxt = cxt + (name -> valTy)
        infer(newEnv, newCxt, next)
      else throw new Exception(s"$body is not of type $valTy")
    else throw new Exception(s"$ty is not a type")

def check(env: Env, cxt: Cxt, tm: Term, ty: Val): Boolean = (tm, ty) match
  case (Term.Lam(param, body), Val.Pi(cl, ty)) =>
    val value = Val.Var(fresh(env.keys.toList, param))
    check(env + (param -> value), cxt + (param -> ty), body, cl(value))
  case _ =>
    conv(env, infer(env, cxt, tm), ty)