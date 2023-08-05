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

  test("prune.scope.intersect") {
    import prune.scope._
    val raw = ScalaParser.parseInput("""
    -- we use Eq to test unification

    let Eq : {A : U} → A → A → U
        = λ {A} x y. (P : A → U) → P x → P y;
    let refl : {A : U}{x : A} → Eq {A} x x
        = λ _ px. px;
    
    -- inline type annotation
    let the : (A : U) → A → A = λ _ x. x;

    let m : U → U → U → U = _;
    let test = λ a b c. the (Eq (m a b c) (m c b a)) refl;
    U
    """)
    val ctx = Ctx.empty
    val expectedMsg = """At Line 13 Column 54:
    let test = λ a b c. the (Eq (m a b c) (m c b a)) refl;
                                                     ^
When checking or inferring refl:

Can't unify '(P : (_ : U) -> (U)) -> ((_ : P(?54(a)(b)(c))) -> (P(?54(a)(b)(c))))' and '(P : (_ : U) -> (U)) -> ((_ : P(?54(a)(b)(c))) -> (P(?54(c)(b)(a))))':

Values obviously inconsistent"""
    var msg = ""
    try infer(ctx, raw)
    catch case e => msg = e.getMessage()
    assertEquals(msg, expectedMsg)
  }
}
