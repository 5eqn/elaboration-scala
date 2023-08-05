package prune.scope

type MetaID = Int

enum MetaState:
  case Unsolved(ty: Val)
  case Solved(value: Val, ty: Val)

object Meta:
  var map = Map[MetaID, MetaState]()
  var metaCount = -1
  def value(metaID: MetaID): Val = map(metaID) match
    case MetaState.Unsolved(_)      => Val.Meta(metaID)
    case MetaState.Solved(value, _) => value

  // clean meta state for testing
  def init(): Unit =
    map = Map[MetaID, MetaState]()
    metaCount = -1

  // interface for getting type
  def state(metaID: MetaID): MetaState = map(metaID)

  // separate functions for incrementing MetaID and constructing Term
  def create(ty: Val): MetaID =
    metaCount += 1
    map += (metaCount -> MetaState.Unsolved(ty))
    // println(s"?$metaCount: ${ty.read(Ctx.empty)}")
    metaCount
  def fresh(ctx: Ctx, ty: Val): Term =
    val term = Locals.toTerm(ctx.locals, quote(ctx.envLen, ty))
    val meta = create(eval(List(), term))
    Term.Inserted(Term.Meta(meta), ctx.prun)
  def solve(metaID: MetaID, value: Val, ty: Val): Unit =
    // println(s"?$metaID = ${value.read(Ctx.empty)}")
    map += (metaID -> MetaState.Solved(value, ty))
