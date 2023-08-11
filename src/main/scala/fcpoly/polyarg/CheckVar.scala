package fcpoly.polyarg

type CheckID = Int

enum CheckState:
  case Unchecked(ctx: Ctx, raw: Raw, ty: Val, metaID: MetaID)
  case Checked(tm: Term)

object Check:
  var map = Map[CheckID, CheckState]()
  var lastID = -1
  def init(): Unit =
    map = Map[CheckID, CheckState]()
    lastID = -1
  def state(checkID: CheckID): CheckState = map(checkID)
  def create(ctx: Ctx, raw: Raw, ty: Val): CheckID =
    val metaID = Meta.create(ctx, ty)
    lastID += 1
    map += (lastID -> CheckState.Unchecked(ctx, raw, ty, metaID))
    lastID
  def solve(checkID: CheckID, tm: Term): Unit =
    map += (checkID -> CheckState.Checked(tm))
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
  def elim(checkID: CheckID): Unit =
    state(checkID) match
      case CheckState.Unchecked(ctx, raw, expected, metaID) =>
        val (ttm, tty) = infer(ctx, raw)
        val (tm, inferred) = insertPassive(ctx, ttm, tty)
        solve(checkID, tm)
        unifyCatch(ctx, expected, inferred)
        unifyPlaceholder(ctx, tm, metaID)
      case CheckState.Checked(tm) =>
  def retryAll(blocking: Set[CheckID]): Unit = blocking.foreach(retry)
  def elimAll(): Unit = map.foreach((checkID, _) => elim(checkID))
