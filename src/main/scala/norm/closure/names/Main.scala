// Use closure to prevent storing functions in data
package norm.closure.names

type Name = String
type Env = Map[Name, Val]

// in context `env`, \param. body
case class Closure(param: Name, env: Env, body: Term):
  // construct the context of `body` (env + (param -> arg)) and evaluate it
  def apply(arg: Val): Val = eval(env + (param -> arg), body)

enum Term:
  case Var(name: Name)
  case Lam(param: Name, body: Term)
  case App(func: Term, arg: Term)
  case Let(name: Name, body: Term, next: Term)

enum Val:
  case Var(name: Name)
  case App(func: Val, arg: Val)
  case Lam(cl: Closure)

  def apply(u: Val): Val = this match
    case Lam(cl) => cl(u)
    case t       => App(t, u)

def fresh(env: List[Name], x: Name): Name = x match
  case "_"                  => "_"
  case _ if env.contains(x) => fresh(env, x + "'")
  case _                    => x

def eval(env: Env, tm: Term): Val = tm match
  case Term.Var(name) =>
    env.get(name).get
  case Term.Lam(param, body) =>
    Val.Lam(Closure(param, env, body))
  case Term.App(func, arg) =>
    eval(env, func)(eval(env, arg))
  case Term.Let(name, body, next) =>
    eval(env + (name -> eval(env, body)), next)

def quote(ns: List[Name], x: Val): Term = x match
  case Val.Var(name) =>
    Term.Var(name)
  case Val.App(func, arg) =>
    Term.App(quote(ns, func), quote(ns, arg))
  case Val.Lam(cl) =>
    val name = fresh(ns, cl.param)
    Term.Lam(name, quote(name :: ns, cl(Val.Var(name))))

def nf(env: Env, tm: Term): Term = quote(env.keys.toList, eval(env, tm))
