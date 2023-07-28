package typecheck.hoas.names

type Name = String
type Env = Map[Name, Val]
type Cxt = Map[Name, Val]

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
  case Lam(param: Name, value: Val => Val)
  case Pi(param: Name, ty: Val, value: Val => Val)

  def apply(u: Val): Val = this match
    case Lam(_, t) => t(u)
    case t         => App(t, u)

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
    eval(env, func).apply(eval(env, arg))
  case Term.Lam(param, body) =>
    Val.Lam(param, arg => eval(env + (param -> arg), body))
  case Term.Pi(param, ty, body) =>
    Val.Pi(param, eval(env, ty), arg => eval(env + (param -> arg), body))
  case Term.Let(name, ty, body, next) =>
    eval(env + (name -> eval(env, body)), next)

def quote(ns: List[Name], x: Val): Term = x match
  case Val.U =>
    Term.U
  case Val.Var(name) =>
    Term.Var(name)
  case Val.App(func, arg) =>
    Term.App(quote(ns, func), quote(ns, arg))
  case Val.Lam(param, value) =>
    val name = fresh(ns, param)
    Term.Lam(name, quote(name :: ns, value(Val.Var(name))))
  case Val.Pi(param, ty, value) =>
    val name = fresh(ns, param)
    Term.Pi(name, quote(ns, ty), quote(name :: ns, value(Val.Var(name))))

def conv(env: Env, x: Val, y: Val): Boolean = (x, y) match
  case (Val.U, Val.U) =>
    true
  case (Val.Var(x), Val.Var(y)) =>
    x == y
  case (Val.App(x1, x2), Val.App(y1, y2)) =>
    conv(env, x1, y1) && conv(env, x2, y2)
  case (Val.Lam(x1, x2), Val.Lam(y1, y2)) =>
    conv(env, x2(Val.Var(x1)), y2(Val.Var(x1)))
  case (Val.Pi(x1, x2, x3), Val.Pi(y1, y2, y3)) =>
    conv(env, x2, y2) && conv(env, x3(Val.Var(x1)), y3(Val.Var(x1)))
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
      case Val.Pi(_, ty, body) =>
        if check(env, cxt, arg, ty) then body(eval(env, arg))
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
  case (Term.Lam(param, body), Val.Pi(param1, ty1, body1)) =>
    val value = Val.Var(fresh(env.keys.toList, param))
    check(env + (param -> value), cxt + (param -> ty1), body, body1(value))
  case _ =>
    conv(env, infer(env, cxt, tm), ty)
