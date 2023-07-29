// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class NormTest extends munit.FunSuite {
  test("norm.hoas.names") {
    import norm.hoas.names._
    val sampleEnv: Env = Map("a" -> Val.Var("a"), "g" -> Val.Var("g"))
    val sampleTerm: Term = Term.Let(
      "f",
      Term.Lam("x", Term.Var("x")),
      Term.App(Term.Var("f"), Term.App(Term.Var("g"), Term.Var("f")))
    )
    val expectedNormalizedForm: Term =
      Term.App(Term.Var("g"), Term.Lam("x", Term.Var("x")))
    val result = nf(sampleEnv, sampleTerm)
    assertEquals(result, expectedNormalizedForm)
  }

  test("norm.closure.names") {
    import norm.closure.names._
    val sampleEnv: Env = Map("a" -> Val.Var("a"), "g" -> Val.Var("g"))
    val sampleTerm: Term = Term.Let(
      "f",
      Term.Lam("x", Term.Var("x")),
      Term.App(Term.Var("f"), Term.App(Term.Var("g"), Term.Var("f")))
    )
    val expectedNormalizedForm: Term =
      Term.App(Term.Var("g"), Term.Lam("x", Term.Var("x")))
    val result = nf(sampleEnv, sampleTerm)
    assertEquals(result, expectedNormalizedForm)
  }

  test("norm.closure.debruijn") {
    import norm.closure.debruijn._
    val sampleEnv: Env = List(Val.Var(1), Val.Var(0))
    val sampleTerm: Term = Term.Let(
      Term.Lam(Term.Var(0)),
      Term.App(Term.Var(0), Term.App(Term.Var(2), Term.Var(0)))
    )
    val expectedNormalizedForm: Term =
      Term.App(Term.Var(1), Term.Lam(Term.Var(0)))
    val result = nf(sampleEnv, sampleTerm)
    assertEquals(result, expectedNormalizedForm)
  }
}
