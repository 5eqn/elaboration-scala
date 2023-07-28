// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class TestSuite extends munit.FunSuite {
  test("norm.hoas.name") {
    import norm.hoas.name._
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

  test("norm.closure.name") {
    import norm.closure.name._
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

  test("typecheck.hoas.name") {
    import typecheck.hoas.name._
    val env: Env =
      Map(
        "Nat" -> Val.Var("Nat"),
        "S" -> Val.Var("S"),
        "Z" -> Val.Var("Z"),
        "Vect" -> Val.Var("Vect"),
        "Nil" -> Val.Var("Nil"),
        "Cons" -> Val.Var("Cons")
      )
    val cxt: Cxt = Map(
      "Nat" -> Val.U,
      "S" -> Val.Pi("_", Val.Var("Nat"), _ => Val.Var("Nat")),
      "Z" -> Val.Var("Nat"),
      "Vect" -> Val.Pi("_", Val.Var("Nat"), _ => Val.U),
      "Nil" -> Val.App(Val.Var("Vect"), Val.Var("Z")),
      "Cons" -> Val.Pi(
        "n",
        Val.Var("Nat"),
        n =>
          Val.Pi(
            "_",
            Val.App(Val.Var("Vect"), n),
            _ =>
              Val.Pi(
                "_",
                Val.Var("Nat"),
                _ => Val.App(Val.Var("Vect"), Val.App(Val.Var("S"), n))
              )
          )
      )
    )
    val tm: Term = Term.Let(
      "one",
      Term.Var("Nat"),
      Term.App(Term.Var("S"), Term.Var("Z")),
      Term.Let(
        "unaryVect",
        Term.App(Term.Var("Vect"), Term.Var("one")),
        Term.App(
          Term.App(
            Term.App(Term.Var("Cons"), Term.Var("Z")),
            Term.Var("Nil")
          ),
          Term.Var("Z")
        ),
        Term.App(
          Term.App(
            Term.App(Term.Var("Cons"), Term.Var("one")),
            Term.Var("unaryVect")
          ),
          Term.Var("Z")
        )
      )
    )
    val ty: Term = Term.Let(
      "two",
      Term.Var("Nat"),
      Term.App(Term.Var("S"), Term.App(Term.Var("S"), Term.Var("Z"))),
      Term.App(Term.Var("Vect"), Term.Var("two"))
    )
    val tyRes = check(env, cxt, ty, Val.U)
    assertEquals(tyRes, true)
    val valRes = check(env, cxt, tm, eval(env, ty))
    assertEquals(valRes, true)
  }
}
