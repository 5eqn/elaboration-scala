// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class TestSuite extends munit.FunSuite {
  test("norm.hoas.name") {
    import norm.hoas.name._
    val sampleEnv: Env = Map("y" -> Val.Var("y"))
    val sampleTerm: Term = Term.App(Term.Lam("x", Term.Var("x")), Term.Var("y"))
    val expectedNormalizedForm: Term = Term.Var("y")
    val result = nf(sampleEnv, sampleTerm)
    assertEquals(result, expectedNormalizedForm)
  }
  test("norm.closure.name") {
    import norm.closure.name._
    val sampleEnv: Env = Map("y" -> Val.Var("y"))
    val sampleTerm: Term = Term.App(Term.Lam("x", Term.Var("x")), Term.Var("y"))
    val expectedNormalizedForm: Term = Term.Var("y")
    val result = nf(sampleEnv, sampleTerm)
    assertEquals(result, expectedNormalizedForm)
  }
  test("norm.closure.debruijn") {
    import norm.closure.debruijn._
    val sampleEnv: Env = List(Val.Var(0))
    val sampleTerm: Term = Term.App(Term.Lam(Term.Var(0)), Term.Var(1))
    val expectedNormalizedForm: Term = Term.Var(1)
    val result = nf(sampleEnv, sampleTerm)
    assertEquals(result, expectedNormalizedForm)
  }
}
