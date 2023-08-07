// Filter out let-bound variables for better performace.
package holes.filter

type Name = String
type Env = List[Val]
type Spine = List[Val]

type Index = Int
type Level = Int
type MetaID = Int

enum MetaState:
  case Unsolved
  case Solved(value: Val)

type Bindings = List[Binding]

// binding type of variables
enum Binding:
  // bound by Pi or Lam
  case Bound
  // defined by Let, masked out in Meta
  case Defined

// filter defined variables out of env
object Env:
  def filter(env: Env, bd: Bindings) =
    env.zip(bd).filter((v, b) => b == Binding.Bound).map(_._1)

object Meta:
  var map = Map[MetaID, MetaState]()
  var metaCount = -1
  def value(metaID: MetaID): Val = map(metaID) match
    case MetaState.Unsolved      => Val.Meta(metaID)
    case MetaState.Solved(value) => value
  def fresh(ctx: Ctx): Term =
    metaCount += 1
    map += (metaCount -> MetaState.Unsolved)
    Term.Inserted(metaCount, ctx.bindings)
  def solve(metaID: MetaID, value: Val): Unit =
    map += (metaID -> MetaState.Solved(value))

// add a binding field to context
case class Ctx(
    env: Env,
    bindings: Bindings,
    src: Map[Name, (Level, Val)]
):
  // separate `add` to `bind` and `define`
  def bind(name: Name, value: Val, ty: Val): Ctx =
    Ctx(
      value :: env,
      Binding.Bound :: bindings,
      src + (name -> (env.length, ty))
    )
  def bind(name: Name, ty: Val): Ctx =
    bind(name, Val.Var(env.length), ty)
  def define(name: Name, value: Val, ty: Val): Ctx =
    Ctx(
      value :: env,
      Binding.Defined :: bindings,
      src + (name -> (env.length, ty))
    )
  def define(name: Name, ty: Val): Ctx =
    define(name, Val.Var(env.length), ty)
  def envLen: Int = env.length
  def nextVal: Val = Val.Var(env.length)

object Ctx:
  def empty: Ctx = Ctx(List(), List(), Map())

case class Closure(env: Env, body: Term):
  def apply(arg: Val): Val = eval(arg :: env, body)

case class PartialRenaming(cod: Level, dom: Level, map: Map[Int, Level]):
  def lift: PartialRenaming =
    PartialRenaming(cod + 1, dom + 1, map + (cod -> dom))
  def nextCod: Val = Val.Var(cod)

enum Raw:
  case U
  case Hole
  case Var(name: Name)
  case App(func: Raw, arg: Raw)
  case Lam(param: Name, body: Raw)
  case Pi(param: Name, ty: Raw, body: Raw)
  case Let(name: Name, ty: Raw, body: Raw, next: Raw)

enum Term:
  case U
  case Meta(metaID: MetaID)
  case Inserted(metaID: MetaID, bindings: Bindings)
  case Var(index: Index)
  case App(func: Term, arg: Term)
  case Lam(param: Name, body: Term)
  case Pi(param: Name, ty: Term, body: Term)
  case Let(name: Name, ty: Term, body: Term, next: Term)

enum Val:
  case U
  case Flex(metaID: MetaID, spine: Spine)
  case Rigid(level: Level, spine: Spine)
  case Lam(param: Name, cl: Closure)
  case Pi(param: Name, ty: Val, cl: Closure)

  def apply(u: Val): Val = this match
    case Lam(param, cl)      => cl(u)
    case Rigid(level, spine) => Rigid(level, u :: spine)
    case Flex(metaID, spine) => Flex(metaID, u :: spine)
    case _                   => throw new Exception("impossible")

  def apply(sp: Spine): Val =
    sp.foldRight(this)((value, term) => term(value))

  def force: Val = this match
    case Flex(metaID, spine) =>
      Meta.map(metaID) match
        case MetaState.Unsolved      => this
        case MetaState.Solved(value) => value(spine).force
    case _ => this

object Val:
  def Var(level: Level): Val = Rigid(level, List())
  def Meta(metaID: MetaID): Val = Flex(metaID, List())

def eval(env: Env, tm: Term): Val = tm match
  case Term.U =>
    Val.U
  case Term.Inserted(metaID, bindings) =>
    // filter env here
    Meta.value(metaID)(Env.filter(env, bindings))
  case Term.Meta(metaID) =>
    Meta.value(metaID)
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

def quote(envLen: Level, x: Val): Term =
  val quoteSp = (spine: Spine, initialTerm: Term) =>
    spine.foldRight(initialTerm)((value, term) =>
      Term.App(term, quote(envLen, value))
    )
  x.force match
    case Val.U =>
      Term.U
    case Val.Flex(metaID, spine) =>
      quoteSp(spine, Term.Meta(metaID))
    case Val.Rigid(level, spine) =>
      quoteSp(spine, Term.Var(envLen - level - 1))
    case Val.Lam(param, cl) =>
      Term.Lam(param, quote(envLen + 1, cl(Val.Var(envLen))))
    case Val.Pi(param, ty, cl) =>
      Term.Pi(
        param,
        quote(envLen, ty),
        quote(envLen + 1, cl(Val.Var(envLen)))
      )

def invert(envLen: Level, spine: Spine): PartialRenaming =
  spine.foldRight(PartialRenaming(envLen, 0, Map()))((value, pr) =>
    value.force match
      case Val.Rigid(level, List()) =>
        PartialRenaming(pr.cod, pr.dom + 1, pr.map + (level -> pr.dom))
      case _ =>
        PartialRenaming(pr.cod, pr.dom + 1, pr.map)
  )

def rename(lhs: MetaID, pr: PartialRenaming, value: Val): Term =
  val renameSp = (spine: Spine, initialTerm: Term) =>
    spine.foldRight(initialTerm)((value, term) =>
      Term.App(term, rename(lhs, pr, value))
    )
  value.force match
    case Val.U =>
      Term.U
    case Val.Flex(rhs, spine) =>
      if rhs == lhs then throw new Exception(s"$rhs occurs in rhs")
      else renameSp(spine, Term.Meta(rhs))
    case Val.Rigid(level, spine) =>
      renameSp(spine, Term.Var(pr.dom - pr.map(level) - 1))
    case Val.Lam(param, cl) =>
      Term.Lam(param, rename(lhs, pr.lift, cl(pr.nextCod)))
    case Val.Pi(param, ty, cl) =>
      Term.Pi(
        param,
        rename(lhs, pr, ty),
        rename(lhs, pr.lift, cl(pr.nextCod))
      )

def solve(lhs: MetaID, envLen: Level, sp: Spine, rhs: Val): Unit =
  val pr = invert(envLen, sp)
  val tm = rename(lhs, pr, rhs)
  Meta.solve(
    lhs,
    eval(
      List(),
      (0 until pr.dom).foldRight(tm)((lvl, term) => Term.Lam("x" + lvl, term))
    )
  )

def unify(envLen: Level, x: Val, y: Val): Unit =
  val unifySp = (x: Spine, y: Spine) =>
    if x.length != y.length then throw new Exception("spine length mismatch")
    x.zip(y).map((lhs, rhs) => unify(envLen, lhs, rhs))
  (x.force, y.force) match
    case (Val.U, Val.U) =>
    case (Val.Flex(x, spx), Val.Flex(y, spy)) if x == y =>
      unifySp(spx, spy)
    case (Val.Rigid(x, spx), Val.Rigid(y, spy)) if x == y =>
      unifySp(spx, spy)
    case (Val.Flex(id, spine), y) => solve(id, envLen, spine, y)
    case (x, Val.Flex(id, spine)) => solve(id, envLen, spine, x)
    case (Val.Lam(_, cl), y) =>
      val value = Val.Var(envLen)
      unify(envLen + 1, cl(value), y(value))
    case (x, Val.Lam(_, cl)) =>
      val value = Val.Var(envLen)
      unify(envLen + 1, x(value), cl(value))
    case (Val.Pi(_, ty1, cl1), Val.Pi(_, ty2, cl2)) =>
      val value = Val.Var(envLen)
      unify(envLen, ty1, ty2)
      unify(
        envLen + 1,
        cl1(value),
        cl2(value)
      )
    case _ => throw new Exception(s"unable to unify $x and $y")

def infer(ctx: Ctx, tm: Raw): (Term, Val) = tm match
  case Raw.U =>
    (Term.U, Val.U)
  case Raw.Hole =>
    (Meta.fresh(ctx), eval(ctx.env, Meta.fresh(ctx)))
  case Raw.Var(name) =>
    val (level, ty) = ctx.src(name)
    (Term.Var(ctx.envLen - level - 1), ty)
  case Raw.App(func, arg) =>
    val (funcTerm, funcType) = infer(ctx, func)
    funcType.force match
      case Val.Pi(_, ty, cl) =>
        val argTerm = check(ctx, arg, ty)
        (Term.App(funcTerm, argTerm), cl(eval(ctx.env, argTerm)))
      case ty =>
        val argTy = eval(ctx.env, Meta.fresh(ctx))
        val tmplCl = Closure(ctx.env, Meta.fresh(ctx.bind("x", argTy)))
        val tmplTy = Val.Pi("x", argTy, tmplCl)
        unify(ctx.envLen, ty, tmplTy)
        val argTerm = check(ctx, arg, argTy)
        (Term.App(funcTerm, argTerm), tmplCl(eval(ctx.env, argTerm)))
  case Raw.Lam(param, body) =>
    val metaVal = eval(ctx.env, Meta.fresh(ctx))
    // use ctx.bind to create a bound variable
    val (bodyTerm, bodyType) = infer(ctx.bind(param, metaVal), body)
    val tyClosure = Closure(ctx.env, quote(ctx.envLen + 1, bodyType))
    (Term.Lam(param, bodyTerm), Val.Pi(param, metaVal, tyClosure))
  case Raw.Pi(param, ty, body) =>
    val tyTerm = check(ctx, ty, Val.U)
    val tyVal = eval(ctx.env, tyTerm)
    val bodyTerm = check(ctx.bind(param, tyVal), body, Val.U)
    (Term.Pi(param, tyTerm, bodyTerm), Val.U)
  case Raw.Let(name, ty, body, next) =>
    val tyTerm = check(ctx, ty, Val.U)
    val tyVal = eval(ctx.env, tyTerm)
    val bodyTerm = check(ctx, body, tyVal)
    val bodyVal = eval(ctx.env, bodyTerm)
    // use ctx.define to create a defined variable
    val (nextTerm, nextTy) = infer(ctx.define(name, bodyVal, tyVal), next)
    (Term.Let(name, tyTerm, bodyTerm, nextTerm), nextTy)

def check(ctx: Ctx, tm: Raw, ty: Val): Term = (tm, ty.force) match
  case (Raw.Hole, _) =>
    Meta.fresh(ctx)
  case (Raw.Lam(param, body), Val.Pi(_, ty, cl)) =>
    val value = ctx.nextVal
    val bodyVal = check(ctx.bind(param, value, ty), body, cl(value))
    Term.Lam(param, bodyVal)
  case (tm, expected) =>
    val (tm2, inferred) = infer(ctx, tm)
    unify(ctx.envLen, expected, inferred)
    tm2
