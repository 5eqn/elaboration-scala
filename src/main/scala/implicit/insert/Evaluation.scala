package `implicit`.insert

def eval(env: Env, tm: Term): Val = tm match
  case Term.U =>
    Val.U
  case Term.Inserted(metaID) =>
    Meta.value(metaID)(Spine(env))
  case Term.Meta(metaID) =>
    Meta.value(metaID)
  case Term.Var(index) =>
    env(index)
  case Term.App(func, arg, i) =>
    eval(env, func)(Param(eval(env, arg), i))
  case Term.Lam(param, body, i) =>
    Val.Lam(param, Closure(env, body), i)
  case Term.Pi(param, ty, body, i) =>
    Val.Pi(param, eval(env, ty), Closure(env, body), i)
  case Term.Let(name, ty, body, next) =>
    eval(eval(env, body) :: env, next)

def quote(envLen: Level, x: Val): Term =
  val quoteSp = (spine: Spine, initialTerm: Term) =>
    spine.foldRight(initialTerm)((param, term) =>
      Term.App(term, quote(envLen, param.value), param.icit)
    )
  x.force match
    case Val.U =>
      Term.U
    case Val.Flex(metaID, spine) =>
      quoteSp(spine, Term.Meta(metaID))
    case Val.Rigid(level, spine) =>
      quoteSp(spine, Term.Var(envLen - level - 1))
    case Val.Lam(param, cl, i) =>
      Term.Lam(param, quote(envLen + 1, cl(Val.Var(envLen))), i)
    case Val.Pi(param, ty, cl, i) =>
      Term.Pi(
        param,
        quote(envLen, ty),
        quote(envLen + 1, cl(Val.Var(envLen))),
        i
      )
