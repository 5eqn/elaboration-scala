package commented

type CheckID = Int

// State of checking.
//
// When checking `raw : ?0`, the check will be *deferred*,
// `raw = ?metaID [ctx]` will be assumed as placeholder,
// arguments of `check` function will be stored for *retrying*.
//
// If retry succeeds, store check result in the state,
// so that result can be directly accessed.
enum CheckState:
  case Unchecked(ctx: Ctx, raw: Raw, ty: Val, metaID: MetaID)
  case Checked(tm: Term)

// Object of checking, encapsulates CRUD for delayed check problems.
object Check:
  var map = Map[CheckID, CheckState]()
  var lastID = -1

  // initialize checking state, called before check
  def init(): Unit =
    map = Map[CheckID, CheckState]()
    lastID = -1

  // CheckID -> CheckState
  def state(checkID: CheckID): CheckState = map(checkID)

  // defer a check
  def create(ctx: Ctx, raw: Raw, ty: Val): CheckID =
    val metaID = Meta.create(ctx, ty)
    lastID += 1
    map += (lastID -> CheckState.Unchecked(ctx, raw, ty, metaID))
    lastID

  // (internal) solve a check
  def solve(checkID: CheckID, tm: Term): Unit =
    map += (checkID -> CheckState.Checked(tm))

  // retry a check, assume implicit insertion can happen
  def retry(checkID: CheckID): Unit =
    state(checkID) match
      case CheckState.Unchecked(ctx, raw, ty, metaID) =>
        ty.force match
          case Val.Flex(newMetaID, _) =>
            Meta.transfer(newMetaID, checkID)
          case _ =>
            val tm = check(ctx, raw, ty)
            solve(checkID, tm)
            unifyPlaceholder(ctx, tm, metaID)
      case CheckState.Checked(tm) =>

  // eliminate a check, assume there's no implicit insertion
  def elim(checkID: CheckID): Unit =
    state(checkID) match
      case CheckState.Unchecked(ctx, raw, expected, metaID) =>
        val (ttm, tty) = infer(ctx, raw)
        val (tm, inferred) = insertPassive(ctx, ttm, tty)
        solve(checkID, tm)
        unifyCatch(ctx, expected, inferred)
        unifyPlaceholder(ctx, tm, metaID)
      case CheckState.Checked(tm) =>

  // retry all checkes in a `blocking`
  def retryAll(blocking: Set[CheckID]): Unit = blocking.foreach(retry)

  // eliminate all checkes, called after check
  def elimAll(): Unit = map.foreach((checkID, _) => elim(checkID))
