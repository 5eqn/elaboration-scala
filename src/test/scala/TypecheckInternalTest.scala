// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class TypecheckInternalTest extends munit.FunSuite {
  test("typecheck.hoas.env.names") {
    import typecheck.hoas.names._
    val env: Env = Map(
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

  test("typecheck.hoas.lambda.vect") {
    import typecheck.hoas.names._
    val env: Env = Map()
    val cxt: Cxt = Map()
    val tm: Term = Term.Lam(
      "Nat",
      Term.Lam(
        "S",
        Term.Lam(
          "Z",
          Term.Lam(
            "Vect",
            Term.Lam(
              "Nil",
              Term.Lam(
                "Cons",
                Term.Let(
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
              )
            )
          )
        )
      )
    )
    val ty: Term = Term.Pi(
      "Nat",
      Term.U,
      Term.Pi(
        "S",
        Term.Pi("_", Term.Var("Nat"), Term.Var("Nat")),
        Term.Pi(
          "Z",
          Term.Var("Nat"),
          Term.Pi(
            "Vect",
            Term.Pi("_", Term.Var("Nat"), Term.U),
            Term.Pi(
              "Nil",
              Term.App(Term.Var("Vect"), Term.Var("Z")),
              Term.Pi(
                "Cons",
                Term.Pi(
                  "n",
                  Term.Var("Nat"),
                  Term.Pi(
                    "_",
                    Term.App(Term.Var("Vect"), Term.Var("n")),
                    Term.Pi(
                      "_",
                      Term.Var("Nat"),
                      Term.App(
                        Term.Var("Vect"),
                        Term.App(Term.Var("S"), Term.Var("n"))
                      )
                    )
                  )
                ),
                Term.Let(
                  "two",
                  Term.Var("Nat"),
                  Term
                    .App(Term.Var("S"), Term.App(Term.Var("S"), Term.Var("Z"))),
                  Term.App(Term.Var("Vect"), Term.Var("two"))
                )
              )
            )
          )
        )
      )
    )
    val tyRes = check(env, cxt, ty, Val.U)
    assertEquals(tyRes, true)
    val valRes = check(env, cxt, tm, eval(env, ty))
    assertEquals(valRes, true)
  }

  test("typecheck.closure.names.env.vect") {
    import typecheck.closure.names._
    val env: Env = Map(
      "Nat" -> Val.Var("Nat"),
      "S" -> Val.Var("S"),
      "Z" -> Val.Var("Z"),
      "Vect" -> Val.Var("Vect"),
      "Nil" -> Val.Var("Nil"),
      "Cons" -> Val.Var("Cons")
    )
    val cxt: Cxt = Map(
      "Nat" -> Val.U,
      "S" -> Val.Pi(Closure("_", env, Term.Var("Nat")), Val.Var("Nat")),
      "Z" -> Val.Var("Nat"),
      "Vect" -> Val.Pi(Closure("_", env, Term.U), Val.Var("Nat")),
      "Nil" -> Val.App(Val.Var("Vect"), Val.Var("Z")),
      "Cons" -> Val.Pi(
        Closure(
          "n",
          env,
          Term.Pi(
            "_",
            Term.App(Term.Var("Vect"), Term.Var("n")),
            Term.Pi(
              "_",
              Term.Var("Nat"),
              Term.App(Term.Var("Vect"), Term.App(Term.Var("S"), Term.Var("n")))
            )
          )
        ),
        Val.Var("Nat")
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

  test("typecheck.closure.names.env.eta") {
    import typecheck.closure.names._
    val env: Env = Map(
      "A" -> Val.Var("A"),
      "f" -> Val.Var("f"),
      "B" -> Val.Var("B"),
      "MkB" -> Val.Var("MkB")
    )
    val cxt: Cxt = Map(
      "A" -> Val.U,
      "f" -> Val.Pi(Closure("_", env, Term.Var("A")), Val.Var("A")),
      "B" -> Val.Pi(
        Closure("_", env, Term.U),
        Val.Pi(Closure("_", env, Term.Var("A")), Val.Var("A"))
      ),
      "MkB" -> Val.App(
        Val.Var("B"),
        Val.Lam(Closure("x", env, Term.App(Term.Var("f"), Term.Var("x"))))
      )
    )
    val tm: Term = Term.Var("MkB")
    val ty: Term = Term.App(Term.Var("B"), Term.Var("f"))
    val tyRes = check(env, cxt, ty, Val.U)
    assertEquals(tyRes, true)
    val valRes = check(env, cxt, tm, eval(env, ty))
    assertEquals(valRes, true)
  }

  test("typecheck.closure.debruijn.env.vect") {
    import typecheck.closure.debruijn._
    val env: Env = List(
      Val.Var(5),
      Val.Var(4),
      Val.Var(3),
      Val.Var(2),
      Val.Var(1),
      Val.Var(0)
    )
    // these are defined mutually so it's not broken
    val cxt: Cxt = Map(
      "Nat" -> (5, Val.U),
      "S" -> (4, Val.Pi("_", Val.Var(5), Closure(env, Term.Var(1)))),
      "Z" -> (3, Val.Var(5)),
      "Vect" -> (2, Val.Pi("_", Val.Var(5), Closure(env, Term.U))),
      "Nil" -> (1, Val.App(Val.Var(2), Val.Var(3))),
      "Cons" -> (0, Val.Pi(
        "n",
        Val.Var(5),
        Closure(
          env,
          Term.Pi(
            "_",
            Term.App(Term.Var(4), Term.Var(0)),
            Term.Pi(
              "_",
              Term.Var(2),
              Term.App(
                Term.Var(6),
                Term.App(Term.Var(4), Term.Var(2))
              )
            )
          )
        )
      ))
    )
    val tm: Raw = Raw.Let(
      "one",
      Raw.Var("Nat"),
      Raw.App(Raw.Var("S"), Raw.Var("Z")),
      Raw.Let(
        "unaryVect",
        Raw.App(Raw.Var("Vect"), Raw.Var("one")),
        Raw.App(
          Raw.App(
            Raw.App(Raw.Var("Cons"), Raw.Var("Z")),
            Raw.Var("Nil")
          ),
          Raw.Var("Z")
        ),
        Raw.App(
          Raw.App(
            Raw.App(Raw.Var("Cons"), Raw.Var("one")),
            Raw.Var("unaryVect")
          ),
          Raw.Var("Z")
        )
      )
    )
    val ty = Raw.Let(
      "two",
      Raw.Var("Nat"),
      Raw.App(Raw.Var("S"), Raw.App(Raw.Var("S"), Raw.Var("Z"))),
      Raw.App(Raw.Var("Vect"), Raw.Var("two"))
    )
    val tyTerm = check(env, cxt, ty, Val.U)
    val valTerm = check(env, cxt, tm, eval(env, tyTerm))
  }
}
