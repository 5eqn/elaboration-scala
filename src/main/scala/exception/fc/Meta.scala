package exception.fc

type MetaID = Int

enum MetaState:
  case Unsolved
  case Solved(value: Val)

object Meta:
  var map = Map[MetaID, MetaState]()
  var metaCount = -1
  def value(metaID: MetaID): Val = map(metaID) match
    case MetaState.Unsolved      => Val.Meta(metaID)
    case MetaState.Solved(value) => value
  def fresh: Term =
    metaCount += 1
    map += (metaCount -> MetaState.Unsolved)
    Term.Inserted(metaCount)
  def solve(metaID: MetaID, value: Val): Unit =
    map += (metaID -> MetaState.Solved(value))
