// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class TypecheckParsedTest extends munit.FunSuite {
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

  test("typecheck.hoas.names.parsed.polomorphic") {
    import typecheck.hoas.names._
    val raw = ScalaParser.parseInput("""
    let id : (A : U) -> A -> A
      = \A x. x;
    let const : (A B : U) -> A -> B -> A
      = \A B x y. x;
    id ((A B : U) -> A -> B -> A) const""")
    val env: Env = Map()
    val cxt: Cxt = Map()
    val term = infer(env, cxt, raw)
  }

  test("typecheck.hoas.names.parsed.church") {
    import typecheck.hoas.names._
    val raw = ScalaParser.parseInput("""
    let Nat  : U = (N : U) -> (N -> N) -> N -> N;
    let five : Nat = \N s z. s (s (s (s (s z))));
    let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
    let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;
    let ten      : Nat = add five five;
    let hundred  : Nat = mul ten ten;
    let thousand : Nat = mul ten hundred;
    thousand""")
    val env: Env = Map()
    val cxt: Cxt = Map()
    val term = infer(env, cxt, raw)
  }

  test("typecheck.closure.names.parsed.vect") {
    import typecheck.closure.names._
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

  test("typecheck.closure.names.parsed.polomorphic") {
    import typecheck.closure.names._
    val raw = ScalaParser.parseInput("""
    let id : (A : U) -> A -> A
      = \A x. x;
    let const : (A B : U) -> A -> B -> A
      = \A B x y. x;
    id ((A B : U) -> A -> B -> A) const""")
    val env: Env = Map()
    val cxt: Cxt = Map()
    val term = infer(env, cxt, raw)
  }

  test("typecheck.closure.names.parsed.church") {
    import typecheck.closure.names._
    val raw = ScalaParser.parseInput("""
    let Nat  : U = (N : U) -> (N -> N) -> N -> N;
    let five : Nat = \N s z. s (s (s (s (s z))));
    let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
    let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;
    let ten      : Nat = add five five;
    let hundred  : Nat = mul ten ten;
    let thousand : Nat = mul ten hundred;
    thousand""")
    val env: Env = Map()
    val cxt: Cxt = Map()
    val term = infer(env, cxt, raw)
  }

  test("typecheck.closure.debruijn.parsed.vect") {
    import typecheck.closure.debruijn._
    val raw = ScalaParser.parseInput("""
    let pair : (N : U) -> (Z : N) -> (S : N -> N) -> 
      (Vect : N -> U) -> (Nil : Vect Z) -> 
      (Cons : (n : N) -> Vect n -> N -> Vect (S n)) -> Vect (S (S Z)) = 
        \N Z S Vect Nil Cons. 
        let one : N = S Z; 
        let unaryVect : Vect one = Cons Z Nil Z; 
        Cons one unaryVect Z;
    pair""")
    val env: Env = List()
    val cxt: Cxt = Map()
    val term = infer(env, cxt, raw)
  }

  test("typecheck.closure.debruijn.parsed.polomorphic") {
    import typecheck.closure.debruijn._
    val raw = ScalaParser.parseInput("""
    let id : (A : U) -> A -> A
      = \A x. x;
    let const : (A B : U) -> A -> B -> A
      = \A B x y. x;
    id ((A B : U) -> A -> B -> A) const""")
    val env: Env = List()
    val cxt: Cxt = Map()
    val term = infer(env, cxt, raw)
  }

  test("typecheck.closure.debruijn.parsed.church") {
    import typecheck.closure.debruijn._
    val raw = ScalaParser.parseInput("""
    let Nat  : U = (N : U) -> (N -> N) -> N -> N;
    let five : Nat = \N s z. s (s (s (s (s z))));
    let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
    let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;
    let ten      : Nat = add five five;
    let hundred  : Nat = mul ten ten;
    let thousand : Nat = mul ten hundred;
    thousand""")
    val env: Env = List()
    val cxt: Cxt = Map()
    val term = infer(env, cxt, raw)
  }
}
