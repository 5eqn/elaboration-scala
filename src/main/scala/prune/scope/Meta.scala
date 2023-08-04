package prune.scope

type MetaID = Int

// add type to metas
enum MetaState:
  case Unsolved(ty: Val)
  case Solved(value: Val, ty: Val)

object Meta:
  var map = Map[MetaID, MetaState]()
  var metaCount = -1
  def value(metaID: MetaID): Val = map(metaID) match
    case MetaState.Unsolved(_)      => Val.Meta(metaID)
    case MetaState.Solved(value, _) => value

  // interface for getting type
  def state(metaID: MetaID): MetaState = map(metaID)

  // manipulating `Meta`s require type now
  def create(ty: Val): Term =
    metaCount += 1
    map += (metaCount -> MetaState.Unsolved(ty))
    // println(s"?$metaCount: ${ty.read(Ctx.empty)}")
    Term.Meta(metaCount)
  def fresh(ctx: Ctx, ty: Val): Term =
    val term = Locals.toTerm(ctx.locals, quote(ctx.envLen, ty))
    val meta = create(eval(List(), term))
    Term.Inserted(meta, ctx.prun)
  def solve(metaID: MetaID, value: Val, ty: Val): Unit =
    // println(s"?$metaID = ${value.read(Ctx.empty)}")
    map += (metaID -> MetaState.Solved(value, ty))
