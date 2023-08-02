// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class HoleTest extends munit.FunSuite {
  test("holes.spine.vect") {
    import holes.spine._
    val raw = ScalaParser.parseInput("""
    let pair : (N : U) -> (Z : N) -> (S : N -> N) -> 
      (Vect : N -> U) -> (Nil : Vect Z) -> 
      (Cons : (n : N) -> Vect n -> N -> Vect (S n)) -> Vect (S (S Z)) = 
        \N Z S Vect Nil Cons. 
        let one : N = S Z; 
        let unaryVect : Vect one = Cons Z Nil Z; 
        Cons one unaryVect Z;
    pair""")
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.spine.polymorphic") {
    import holes.spine._
    val raw = ScalaParser.parseInput("""
    let id : (A : U) -> A -> A
      = \A x. x;
    let const : (A B : U) -> A -> B -> A
      = \A B x y. x;
    id ((A B : U) -> A -> B -> A) const""")
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.spine.church") {
    import holes.spine._
    val raw = ScalaParser.parseInput("""
    let Nat  : U = (N : U) -> (N -> N) -> N -> N;
    let five : Nat = \N s z. s (s (s (s (s z))));
    let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
    let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;
    let ten      : Nat = add five five;
    let hundred  : Nat = mul ten ten;
    let thousand : Nat = mul ten hundred;
    thousand""")
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.assemble.vect") {
    import holes.assemble._
    val raw = ScalaParser.parseInput("""
    let pair : (N : U) -> (Z : N) -> (S : N -> N) -> 
      (Vect : N -> U) -> (Nil : Vect Z) -> 
      (Cons : (n : N) -> Vect n -> N -> Vect (S n)) -> Vect (S (S Z)) = 
        \N Z S Vect Nil Cons. 
        let one : N = S Z; 
        let unaryVect : Vect one = Cons Z Nil Z; 
        Cons one unaryVect Z;
    pair""")
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.assemble.polymorphic") {
    import holes.assemble._
    val raw = ScalaParser.parseInput("""
    let id : (A : U) -> A -> A
      = \A x. x;
    let const : (A B : U) -> A -> B -> A
      = \A B x y. x;
    id ((A B : U) -> A -> B -> A) const""")
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.assemble.church") {
    import holes.assemble._
    val raw = ScalaParser.parseInput("""
    let Nat  : U = (N : U) -> (N -> N) -> N -> N;
    let five : Nat = \N s z. s (s (s (s (s z))));
    let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
    let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;
    let ten      : Nat = add five five;
    let hundred  : Nat = mul ten ten;
    let thousand : Nat = mul ten hundred;
    thousand""")
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.renaming") {
    import holes.renaming._
    val lhsRaw = ScalaParser.parseInput("""f x y""")
    val ctx0 = Ctx.empty
    val ctx1 = ctx0.add("A", Val.Var(0), Val.U)
    val ctx2 = ctx1.add(
      "f",
      Val.Var(1),
      Val.Pi(
        "_",
        Val.Var(0),
        Closure(ctx1.env, Term.Pi("_", Term.Var(1), Term.Var(2)))
      )
    )
    val ctx3 = ctx2.add("x", Val.Var(2), Val.Var(0))
    val ctx = ctx3.add("y", Val.Var(3), Val.Var(0))
    val lhsVal = eval(ctx.env, infer(ctx, lhsRaw)._1)
    val expectedLhsSpine = List(
      Val.Rigid(
        level = 3,
        spine = Nil
      ),
      Val.Rigid(
        level = 2,
        spine = Nil
      )
    )
    val expectedLhs = Val.Rigid(
      level = 1,
      spine = expectedLhsSpine
    )
    assertEquals(lhsVal, expectedLhs)
    val rhsRaw = ScalaParser.parseInput("""
    let g : A -> A = \z. x; g""")
    val rhsVal = eval(ctx.env, infer(ctx, rhsRaw)._1)
    val expectedRhs = Val.Lam(
      param = "z",
      cl = Closure(
        env = List(
          Val.Rigid(
            level = 3,
            spine = Nil
          ),
          Val.Rigid(
            level = 2,
            spine = Nil
          ),
          Val.Rigid(
            level = 1,
            spine = Nil
          ),
          Val.Rigid(
            level = 0,
            spine = Nil
          )
        ),
        body = Term.Var(
          index = 2
        )
      )
    )
    assertEquals(rhsVal, expectedRhs)
    val solution = solve(ctx.envLen, expectedLhsSpine, expectedRhs)
    val expected = Val.Lam(
      param = "x0",
      cl = Closure(
        env = Nil,
        body = Term.Lam(
          param = "x1",
          body = Term.Lam(
            param = "z",
            body = Term.Var(
              index = 2
            )
          )
        )
      )
    )
    assertEquals(solution, expected)
  }

  test("holes.meta.polymorphic") {
    import holes.meta._
    val raw = ScalaParser.parseInput("""
    let id : (A : U) -> A -> A
      = \A x. x;
    let const : (A B : U) -> A -> B -> A
      = \A B x y. x;
    id ((A B : U) -> A -> B -> A) const""")
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.meta.solve") {
    import holes.meta._
    val raw = ScalaParser.parseInput(solveTest)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.filter.solve") {
    import holes.meta._
    val raw = ScalaParser.parseInput(solveTest)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }
}
