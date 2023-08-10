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

  test("fcpoly.defer.fcpoly") {
    import fcpoly.defer._
    Meta.init()
    val raw = ScalaParser.parseInput("""
    let Maybe : U → U = \A. {M : U → U} → ({A} → A → M A) → ({A} → M A) → M A;
    let foo : Maybe ({A} → A → A) = \Just Nothing. Just (λ x. x);
    U
    """)
    val ctx = Ctx.empty
    val (tm, ty) = infer(ctx, raw)
    // manually retry here, because there's
    // no blocking tracker to "auto retry"
    Check.retryAll()
    Check.elimAll()
    val ms = Meta.read
    val ems = """?0 : (A : U) -> ((M : (_ : U) -> (U)) -> (U)) = λA. λM. U
?1 : (A : U) -> ((M : (_ : U) -> (U)) -> ((_ : {A : U} -> ((_ : A) -> (M(A)))) -> (U))) = λA. λM. λx2. U
?2 : U = U
?3 : (M : (_ : U) -> (U)) -> ((Just : {A : U} -> ((_ : A) -> (M(A)))) -> ((Nothing : {A : U} -> (M(A))) -> (U))) = λM. λJust. λNothing. {A : U} -> ((_ : A) -> (A))
?4 : (M : (_ : U) -> (U)) -> ((Just : {A : U} -> ((_ : A) -> (M(A)))) -> ((Nothing : {A : U} -> (M(A))) -> ({A : U} -> ((_ : A) -> (A))))) = λM. λJust. λNothing. λ{A}. λx. x
"""
    assertEquals(ms, ems)
    val ts = tm.read(ctx)
    val ets =
      """let Maybe : (_ : U) -> (U) = λA. {M : (_ : U) -> (U)} -> ((_ : {A : ?0 A M} -> ((_ : A) -> (M(A)))) -> ((_ : {A : ?1 A M _} -> (M(A))) -> (M(A))));
let foo : Maybe({A : ?2 Maybe} -> ((_ : A) -> (A))) = λ{M}. λJust. λNothing. Just{?3 Maybe M Just Nothing}(λ{A}. λx. x);
U"""
    assertEquals(ts, ets)
  }
}
