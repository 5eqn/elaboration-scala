// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class ExceptionTest extends munit.FunSuite {
  test("exception.catch.insert") {
    import exception.`catch`._
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

  test("exception.catch.unify") {
    import exception.`catch`._
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

Can't unify 'auto#B(a)' and 'auto#A':

Values obviously inconsistent"""
    var msg = ""
    try infer(ctx, raw)
    catch case e => msg = e.getMessage()
    assertEquals(msg, expectedMsg)
  }
}
