package commented

type MetaID = Int

// State of meta variables, or unknown variables.
//
// Unsolved metas store its type, and checking problems blocked on it;
// Solved metas store its type and value.
enum MetaState:
  case Unsolved(blocking: Set[CheckID], ty: Val)
  case Solved(value: Val, ty: Val)

// Object of meta variables, encapsulates CRUD for them.
object Meta:
  var map = Map[MetaID, MetaState]()
  var metaCount = -1

  // get value from metaID
  def value(metaID: MetaID): Val = map(metaID) match
    case MetaState.Unsolved(_, _)   => Val.Meta(metaID)
    case MetaState.Solved(value, _) => value

  // initialize meta state, call before check
  def init(): Unit =
    map = Map[MetaID, MetaState]()
    metaCount = -1

  // get direct state
  def state(metaID: MetaID): MetaState = map(metaID)

  // create an unknown meta with blocking
  def create(ty: Val, blocking: Set[CheckID]): MetaID =
    metaCount += 1
    map += (metaCount -> MetaState.Unsolved(blocking, ty))
    metaCount

  // create an unknown meta with context
  // meta type will be wrapped with "Pi"s over bound variables
  def create(ctx: Ctx, ty: Val): MetaID =
    val term = Locals.toTerm(ctx.locals, quote(ctx.envLen, ty))
    create(eval(List(), term), Set())

  // create an unknown meta and return it's term
  def fresh(ctx: Ctx, ty: Val): Term =
    val meta = create(ctx, ty)
    Term.Inserted(Term.Meta(meta), ctx.prun)

  // solve a meta with given value and type
  def solve(metaID: MetaID, value: Val, ty: Val): Unit =
    map += (metaID -> MetaState.Solved(value, ty))

  // transfer a checking problem to a meta
  def transfer(metaID: MetaID, prob: CheckID): Unit =
    map(metaID) match
      case MetaState.Unsolved(blocking, ty) =>
        map += (metaID -> MetaState.Unsolved(blocking + prob, ty))
      case MetaState.Solved(value, ty) =>
        throw new Exception("impossible")

  // serialize all metas
  def read: String =
    var res = ""
    map.toList.sortBy(_._1).foreach {
      case (metaID, MetaState.Unsolved(_, ty)) =>
        res += s"?$metaID : ${ty.read(Ctx.empty)}\n"
      case (metaID, MetaState.Solved(value, ty)) =>
        res += s"?$metaID : ${ty.read(Ctx.empty)} = ${value.read(Ctx.empty)}\n"
    }
    res
