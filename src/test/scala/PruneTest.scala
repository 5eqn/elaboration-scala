// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class PruneTest extends munit.FunSuite {
  test("prune.typed.insert") {
    import prune.typed._
    val raw = ScalaParser.parseInput(insertTest)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }
  test("prune.scope.prune") {
    import prune.scope._
    val raw = ScalaParser.parseInput("""
      let pr1 = λ f x. f x;
      let pr2 = λ f x y. f x y;
      let pr3 = λ f. f U;

      let pr4 = \f x. f x x x;
      let pr5 = \f g x. f (g x);

      U""")
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }
}
