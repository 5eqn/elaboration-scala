// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class PruneTest extends munit.FunSuite {
  test("prune.typed.insert") {
    import prune.typed._
    val raw = ScalaParser.parseInput(insertTest)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }
}
