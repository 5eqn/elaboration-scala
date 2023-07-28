// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class TestSuite extends munit.FunSuite {
  test("normalize by evaluation") {
    import com.elab.norm.hoas.name._
    val sampleEnv: Env = List(("y", Val.Var("y")))
    val sampleTerm: Term = Term.App(Term.Lam("x", Term.Var("x")), Term.Var("y"))
    val expectedNormalizedForm: Term = Term.Var("y")
    val result = nf(sampleEnv, sampleTerm)
    assertEquals(result, expectedNormalizedForm)
  }
}
