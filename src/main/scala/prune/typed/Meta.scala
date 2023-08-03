package prune.typed

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
  def fresh(ctx: Ctx, ty: Val): Term =
    metaCount += 1
    map += (metaCount -> MetaState.Unsolved(
      eval(List(), Locals.toTerm(ctx.locals, quote(ctx.envLen, ty)))
    ))
    Term.Inserted(metaCount, ctx.prun)
  def solve(metaID: MetaID, value: Val, ty: Val): Unit =
    map += (metaID -> MetaState.Solved(value, ty))