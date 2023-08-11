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
    Check.init()
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
let foo : Maybe({A : ?2} -> ((_ : A) -> (A))) = λ{M}. λJust. λNothing. Just{?3 M Just Nothing}(λ{A}. λx. x);
U"""
    assertEquals(ts, ets)
  }

  test("fcpoly.block.fcpoly") {
    import fcpoly.block._
    Meta.init()
    Check.init()
    val raw = ScalaParser.parseInput("""
    let Maybe : U → U = \A. {M : U → U} → ({A} → A → M A) → ({A} → M A) → M A;
    let foo : Maybe ({A} → A → A) = \Just Nothing. Just (λ x. x);
    U
    """)
    val ctx = Ctx.empty
    val (tm, ty) = infer(ctx, raw)
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
let foo : Maybe({A : ?2} -> ((_ : A) -> (A))) = λ{M}. λJust. λNothing. Just{?3 M Just Nothing}(λ{A}. λx. x);
U"""
    assertEquals(ts, ets)
  }

  test("fcpoly.block.full") {
    import fcpoly.block._
    Meta.init()
    Check.init()
    val raw = ScalaParser.parseInput(fcpolyFullTest)
    val ctx = Ctx.empty
    val (tm, ty) = infer(ctx, raw)
    Check.elimAll()
    val ms = Meta.read
    val ems = fcpolyFullMeta
    assertEquals(ms, ems)
    val ts = tm.read(ctx)
    val ets = fcpolyFullTerm
    assertEquals(ts, ets)
  }

  test("fcpoly.block.polyarg") {
    import fcpoly.block._
    Meta.init()
    Check.init()
    val raw = ScalaParser.parseInput("""
    let tm = λ X Y a. λ (f : ({_ : X} -> Y) -> (X -> Y) -> U). f(a)(λ x. a {x});
    U
    """)
    val ctx = Ctx.empty
    val err = """At Line 2 Column 74:
    let tm = λ X Y a. λ (f : ({_ : X} -> Y) -> (X -> Y) -> U). f(a)(λ x. a {x});
                                                                         ^
When checking or inferring a{x}:

Can't unify 'Y' and '{x : ?5(X)(Y)(a)(f)(x)} -> (?6(X)(Y)(a)(f)(x)(x))':

Values obviously inconsistent"""
    var msg = ""
    infer(ctx, raw)
    try Check.elimAll()
    catch case e => msg = e.getMessage()
    assertEquals(msg, err)
  }

  test("fcpoly.polyarg.polyarg") {
    import fcpoly.polyarg._
    Meta.init()
    Check.init()
    val raw = ScalaParser.parseInput("""
    let tm = λ X Y a. λ (f : ({_ : X} -> Y) -> (X -> Y) -> U). f(a)(λ x. a {x});
    U
    """)
    val ctx = Ctx.empty
    val (tm, ty) = infer(ctx, raw)
    Check.elimAll()
    val ems = """?0 : U = (X : U) -> ((Y : U) -> ((a : {_ : X} -> (Y)) -> ((f : (_ : {_ : X} -> (Y)) -> ((_ : (_ : X) -> (Y)) -> (U))) -> (U))))
?1 : (X : U) -> ((Y : U) -> ((a : {_ : X} -> (Y)) -> ((f : (_ : {_ : X} -> (Y)) -> ((_ : (_ : X) -> (Y)) -> (U))) -> (U)))) = λX. λY. λa. λf. f(a)(λx. a{x})
?2 : U = U
?3 : (X : U) -> (U) = λX. U
?4 : (X : U) -> ((Y : U) -> (U)) = λX. λY. {_ : X} -> (Y)
"""
    val ets = """let tm : ?0 = λX. λY. λa. λf. f(a)(λx. a{x});
U"""
    val ms = Meta.read
    val ts = tm.read(ctx)
    assertEquals(ms, ems)
    assertEquals(ts, ets)
  }
}
