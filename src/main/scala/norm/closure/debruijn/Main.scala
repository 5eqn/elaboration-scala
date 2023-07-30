// Uses de-Bruijn index
package norm.closure.debruijn

type Env = List[Val]

// newly created is 0, eg. \2. \1. \0. ...
type Index = Int
// first created is 0, eg. \0. \1. \2. ...
type Level = Int

case class Closure(env: Env, body: Term):
  def apply(arg: Val): Val = eval(arg :: env, body)

// there's no need for storing name anymore
enum Term:
  case Var(index: Index)
  case Lam(body: Term)
  case App(func: Term, arg: Term)
  case Let(body: Term, next: Term)

enum Val:
  case Var(level: Level)
  case App(func: Val, arg: Val)
  case Lam(cl: Closure)

  def apply(u: Val): Val = this match
    case Lam(cl) => cl(u)
    case t       => App(t, u)

def eval(env: Env, tm: Term): Val = tm match
  case Term.Var(index) =>
    env(index)
  case Term.Lam(body) =>
    Val.Lam(Closure(env, body))
  case Term.App(func, arg) =>
    eval(env, func)(eval(env, arg))
  case Term.Let(body, next) =>
    eval(eval(env, body) :: env, next)

def quote(envLen: Level, x: Val): Term = x match
  case Val.Var(level) =>
    // Term takes index instead of level
    Term.Var(envLen - level - 1)
  case Val.App(func, arg) =>
    Term.App(quote(envLen, func), quote(envLen, arg))
  case Val.Lam(cl) =>
    // name envLen is 100% safe
    Term.Lam(quote(envLen + 1, cl(Val.Var(envLen))))

def nf(env: Env, tm: Term): Term = quote(env.length, eval(env, tm))
