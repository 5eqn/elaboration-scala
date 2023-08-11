package fcpoly.polyarg

type MetaID = Int

enum MetaState:
  case Unsolved(blocking: Set[CheckID], ty: Val)
  case Solved(value: Val, ty: Val)

object Meta:
  var map = Map[MetaID, MetaState]()
  var metaCount = -1
  def value(metaID: MetaID): Val = map(metaID) match
    case MetaState.Unsolved(_, _)   => Val.Meta(metaID)
    case MetaState.Solved(value, _) => value
  def init(): Unit =
    map = Map[MetaID, MetaState]()
    metaCount = -1
  def state(metaID: MetaID): MetaState = map(metaID)
  def create(ty: Val, blocking: Set[CheckID]): MetaID =
    metaCount += 1
    map += (metaCount -> MetaState.Unsolved(blocking, ty))
    metaCount
  def create(ctx: Ctx, ty: Val): MetaID =
    val term = Locals.toTerm(ctx.locals, quote(ctx.envLen, ty))
    create(eval(List(), term), Set())
  def fresh(ctx: Ctx, ty: Val): Term =
    val meta = create(ctx, ty)
    Term.Inserted(Term.Meta(meta), ctx.prun)
  def solve(metaID: MetaID, value: Val, ty: Val): Unit =
    map += (metaID -> MetaState.Solved(value, ty))
  def transfer(metaID: MetaID, prob: CheckID): Unit =
    map(metaID) match
      case MetaState.Unsolved(blocking, ty) =>
        map += (metaID -> MetaState.Unsolved(blocking + prob, ty))
      case MetaState.Solved(value, ty) =>
        throw new Exception("impossible")
  def read: String =
    var res = ""
    map.toList.sortBy(_._1).foreach {
      case (metaID, MetaState.Unsolved(_, ty)) =>
        res += s"?$metaID : ${ty.read(Ctx.empty)}\n"
      case (metaID, MetaState.Solved(value, ty)) =>
        res += s"?$metaID : ${ty.read(Ctx.empty)} = ${value.read(Ctx.empty)}\n"
    }
    res
