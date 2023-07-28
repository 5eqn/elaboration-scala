package norm.closure.debruijn

type Env = List[Val]
type Index = Int
type Level = Int

case class Closure(env: Env, body: Term):
  def apply(arg: Val): Val = eval(arg :: env, body)

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
    case Lam(cl) => cl.apply(u)
    case t       => App(t, u)

def eval(env: Env, tm: Term): Val = tm match
  case Term.Var(index) =>
    env.apply(index)
  case Term.Lam(body) =>
    Val.Lam(Closure(env, body))
  case Term.App(func, arg) =>
    eval(env, func).apply(eval(env, arg))
  case Term.Let(body, next) =>
    eval(eval(env, body) :: env, next)

def quote(envLen: Int, x: Val): Term = x match
  case Val.Var(level) =>
    Term.Var(envLen - level - 1)
  case Val.App(func, arg) =>
    Term.App(quote(envLen, func), quote(envLen, arg))
  case Val.Lam(cl) =>
    Term.Lam(quote(envLen + 1, cl.apply(Val.Var(envLen))))

def nf(env: Env, tm: Term): Term = quote(env.length, eval(env, tm))
