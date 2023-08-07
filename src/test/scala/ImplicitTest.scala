// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class ImplicitTest extends munit.FunSuite {
  test("implicit.modularize.solve") {
    import `implicit`.modularize._
    val raw = ScalaParser.parseInput(solveTest)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("implicit.model.solve") {
    import `implicit`.model._
    val raw = ScalaParser.parseInput(solveTest)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("implicit.insert.solve") {
    import `implicit`.model._
    val raw = ScalaParser.parseInput(solveTest)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("implicit.insert.insert") {
    import `implicit`.insert._
    val raw = ScalaParser.parseInput(insertTest)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("implicit.named.insert") {
    import `implicit`.named._
    val raw = ScalaParser.parseInput(insertTest)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("implicit.catch.named") {
    import `implicit`.`catch`._
    val raw = ScalaParser.parseInput("""
      let f : {A}{B} -> A -> (A -> B) -> B
          = \a f. f a;
      f {B = U} {A = U} U (\x. x)
    """)
    val ctx = Ctx.empty
    val expectedMsg = """At Line 4 Column 7:
      f {B = U} {A = U} U (\x. x)
      ^
When checking or inferring f{B = U}{A = U}:

Can't insert 'f{_}{U}':

Implicit argument A not found"""
    var msg = ""
    try infer(ctx, raw)
    catch case e => msg = e.getMessage()
    assertEquals(msg, expectedMsg)
  }

  test("implicit.catch.unify") {
    import `implicit`.`catch`._
    val raw = ScalaParser.parseInput("""
    let comp : {A}{B : A -> U}{C : {a} -> B a -> U}
               (f : {a}(b : B a) -> C b)
               (g : (a : A) -> B a)
               (a : A)
               -> C (g a)
        = \f g a. g (g a);
    U
    """)
    val ctx = Ctx.empty
    val expectedMsg = """At Line 7 Column 22:
        = \f g a. g (g a);
                     ^
When checking or inferring g(a):

Can't unify 'auto#A' and 'auto#B(a)':

Values obviously inconsistent"""
    var msg = ""
    try infer(ctx, raw)
    catch case e => msg = e.getMessage()
    assertEquals(msg, expectedMsg)
  }

  test("implicit.catch.pruning") {
    import `implicit`.`catch`._
    val raw = ScalaParser.parseInput("""
    let pr = λ f. f U;
    U
    """)
    val ctx = Ctx.empty
    val expectedMsg = """At Line 2 Column 19:
    let pr = λ f. f U;
                  ^
When checking or inferring f(U):

Can't unify '?9' and '(x : ?10(f)) -> (?11(f)(x))':

Pruning is currently not supported"""
    var msg = ""
    try infer(ctx, raw)
    catch case e => msg = e.getMessage()
    assertEquals(msg, expectedMsg)
  }

  test("implicit.catch.insert") {
    import `implicit`.`catch`._
    val raw = ScalaParser.parseInput(insertTest)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("implicit.filter.unify") {
    import `implicit`.filter._
    val raw = ScalaParser.parseInput("""
    let comp : {A}{B : A -> U}{C : {a} -> B a -> U}
               (f : {a}(b : B a) -> C b)
               (g : (a : A) -> B a)
               (a : A)
               -> C (g a)
        = \f g a. g (g a);
    U
    """)
    val ctx = Ctx.empty
    val expectedMsg = """At Line 7 Column 22:
        = \f g a. g (g a);
                     ^
When checking or inferring g(a):

Can't unify 'A' and 'B(a)':

Values obviously inconsistent"""
    var msg = ""
    try infer(ctx, raw)
    catch case e => msg = e.getMessage()
    assertEquals(msg, expectedMsg)
  }

  test("implicit.filter.insert") {
    import `implicit`.filter._
    val raw = ScalaParser.parseInput(insertTest)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }
}
