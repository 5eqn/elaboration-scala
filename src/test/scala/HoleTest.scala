// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class HoleTest extends munit.FunSuite {
  test("holes.spine.parsed.vect") {
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
    val ctx: Ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.spine.parsed.polymorphic") {
    import holes.spine._
    val raw = ScalaParser.parseInput("""
    let id : (A : U) -> A -> A
      = \A x. x;
    let const : (A B : U) -> A -> B -> A
      = \A B x y. x;
    id ((A B : U) -> A -> B -> A) const""")
    val ctx: Ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.spine.parsed.church") {
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
    val ctx: Ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.assemble.parsed.vect") {
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
    val ctx: Ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.assemble.parsed.polymorphic") {
    import holes.assemble._
    val raw = ScalaParser.parseInput("""
    let id : (A : U) -> A -> A
      = \A x. x;
    let const : (A B : U) -> A -> B -> A
      = \A B x y. x;
    id ((A B : U) -> A -> B -> A) const""")
    val ctx: Ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("holes.assemble.parsed.church") {
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
    val ctx: Ctx = Ctx.empty
    val term = infer(ctx, raw)
  }
}
