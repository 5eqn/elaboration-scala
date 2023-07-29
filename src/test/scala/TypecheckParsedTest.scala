// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class TypecheckParsedTest extends munit.FunSuite {
  test("typecheck.hoas.names.parsed.vect") {
    import typecheck.hoas.names._
    val raw = ScalaParser.parseInput("""
    let pair : (N : U) -> (Z : N) -> (S : N -> N) -> 
      (Vect : N -> U) -> (Nil : Vect Z) -> 
      (Cons : (n : N) -> Vect n -> N -> Vect (S n)) -> Vect (S (S Z)) = 
        \N Z S Vect Nil Cons. 
        let one : N = S Z; 
        let unaryVect : Vect one = Cons Z Nil Z; 
        Cons one unaryVect Z;
    pair""")
    val env: Env = Map()
    val cxt: Cxt = Map()
    val term = infer(env, cxt, raw)
  }

  test("typecheck.closure.debruijn.parser") {
    import typecheck.closure.debruijn._
    val raw = ScalaParser.parseInput(
      """let id : (A : U) -> A -> A = \A x. x;
         id"""
    )
    val expectedRaw = Raw.Let(
      name = "id",
      ty = Raw.Pi(
        param = "A",
        ty = Raw.U,
        body = Raw.Pi(
          param = "_",
          ty = Raw.Var("A"),
          body = Raw.Var("A")
        )
      ),
      body = Raw.Lam(
        param = "A",
        body = Raw.Lam(
          param = "x",
          body = Raw.Var("x")
        )
      ),
      next = Raw.Var("id")
    )
    assertEquals(raw, expectedRaw)
  }
}
