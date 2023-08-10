package fcpoly.defer

type CheckID = Int

enum CheckState:
  // ctx, raw, ty: params of check
  // metaID: id of placeholder
  case Unchecked(ctx: Ctx, raw: Raw, ty: Val, metaID: MetaID)
  case Checked(tm: Term)

object Check:
  var map = Map[CheckID, CheckState]()
  var lastID = -1
  def init(): Unit =
    map = Map[CheckID, CheckState]()
    lastID = -1
  def state(checkID: CheckID): CheckState = map(checkID)

  // when checking `raw : unknownTy`,
  // we assume `raw = placeholder` and `placeholder : unknownTy`,
  // and postpone checking `raw : unknownTy`.
  def create(ctx: Ctx, raw: Raw, ty: Val): CheckID =
    val metaID = Meta.create(ctx, ty)
    lastID += 1
    map += (lastID -> CheckState.Unchecked(ctx, raw, ty, metaID))
    lastID

  // solve a check problem, similar to meta
  def solve(checkID: CheckID, tm: Term): Unit =
    map += (checkID -> CheckState.Checked(tm))

  // retry a check, it can be blocked again;
  // this function is in fact not called for now,
  // all problems will be posponed to the "last moment",
  // they will be assumed to have no implicit insertion,
  // which means this chapter literally DOES NOTHING.
  def retry(checkID: CheckID): Unit =
    state(checkID) match
      case CheckState.Unchecked(ctx, raw, ty, metaID) =>
        ty.force match
          case Val.Flex(newMetaID, _) =>
            // still blocked by another meta, transfer block in next chapter
            ()
          case _ =>
            // checking unblocked
            val tm = check(ctx, raw, ty)
            solve(checkID, tm)
            unifyPlaceholder(ctx, tm, metaID)
      case CheckState.Checked(tm) =>

  // eliminate a check, it should not be blocked again
  def elim(checkID: CheckID): Unit =
    state(checkID) match
      case CheckState.Unchecked(ctx, raw, expected, metaID) =>
        // force use inferred check
        val (ttm, tty) = infer(ctx, raw)
        val (tm, inferred) = insertPassive(ctx, ttm, tty)
        solve(checkID, tm)
        unifyCatch(ctx, expected, inferred)
        unifyPlaceholder(ctx, tm, metaID)
      case CheckState.Checked(tm) =>

  // retry all check problems
  def retryAll(): Unit = map.foreach((checkID, _) => retry(checkID))

  // eliminate all check problems
  def elimAll(): Unit = map.foreach((checkID, _) => elim(checkID))
