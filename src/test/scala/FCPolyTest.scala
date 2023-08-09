// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class FCPolyTest extends munit.FunSuite {
  test("fcpoly.tylam.tylam") {
    import fcpoly.tylam._
    Meta.init()
    val raw = ScalaParser.parseInput(
      """let x : (A : U) -> (a : A) -> U = \A (a : U). A; U"""
    )
    val ctx = Ctx.empty
    val expectedMsg = """At Line 1 Column 35:
let x : (A : U) -> (a : A) -> U = \A (a : U). A; U
                                  ^
When checking or inferring λ(a : U). A:

Can't unify 'U' and 'A':

Values obviously inconsistent"""
    var msg = ""
    try infer(ctx, raw)
    catch case e => msg = e.getMessage()
    assertEquals(msg, expectedMsg)
  }
}
