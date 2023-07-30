// Beginning of everything.
package norm.hoas.names

type Name = String
type Env = Map[Name, Val]

enum Term:
  // name
  case Var(name: Name)
  // func arg
  case App(func: Term, arg: Term)
  // \param. body
  case Lam(param: Name, body: Term)
  // let name = body; next
  case Let(name: Name, body: Term, next: Term)

enum Val:
  // name
  case Var(name: Name)
  // func arg
  case App(func: Val, arg: Val)
  // (\param. ?) == value
  case Lam(param: Name, value: Val => Val)

  // apply two normalized Val, yields a normalized one
  def apply(u: Val): Val = this match
    case Lam(_, t) => t(u)
    case t         => App(t, u)

// fresh a new variable name from env
def fresh(env: List[Name], x: Name): Name = x match
  case "_"                  => "_"
  case _ if env.contains(x) => fresh(env, x + "'")
  case _                    => x

// Term -> Val
def eval(env: Env, tm: Term): Val = tm match
  case Term.Var(name) =>
    env.get(name).get
  case Term.Lam(param, body) =>
    Val.Lam(param, arg => eval(env + (param -> arg), body))
  case Term.App(func, arg) =>
    eval(env, func)(eval(env, arg))
  case Term.Let(name, body, next) =>
    eval(env + (name -> eval(env, body)), next)

// Val -> Term
def quote(ns: List[Name], x: Val): Term = x match
  case Val.Var(name) =>
    Term.Var(name)
  case Val.App(func, arg) =>
    Term.App(quote(ns, func), quote(ns, arg))
  case Val.Lam(param, value) =>
    val name = fresh(ns, param)
    Term.Lam(name, quote(name :: ns, value(Val.Var(name))))

// eval and quote back
def nf(env: Env, tm: Term): Term = quote(env.keys.toList, eval(env, tm))
