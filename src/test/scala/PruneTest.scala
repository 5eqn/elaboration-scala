// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class PruneTest extends munit.FunSuite {
  test("prune.typed.insert") {
    import prune.typed._
    Meta.init()
    val raw = ScalaParser.parseInput(insertTest)
    val ctx = Ctx.empty
    val (term, ty) = infer(ctx, raw)
    val metaStr = Meta.read
    val expectedMetaStr = """?0 : U = U
?1 : (A : U) -> (U) = λx0. U
?2 : U = U
?3 : (A : U) -> (U) = λx0. U
?4 : U = U
?5 : U = (_ : U) -> (U)
?6 : U = U
?7 : U = U
?8 : (A : U) -> (U) = λx0. x0
?9 : U = {A : U} -> ((x : A) -> (A))
?10 : U = U
?11 : (A : U) -> (U) = λx0. x0
?12 : U = U
?13 : U = U
?14 : (A : U) -> (U) = λx0. x0
?15 : U = U
?16 : U = U
?17 : (A : U) -> (U) = λx0. U
?18 : U = U
?19 : U = U
?20 : U = U
?21 : (A : U) -> (U) = λx0. U
?22 : U = (B : U) -> ((_ : B) -> ((_ : B) -> (B)))
?23 : U = (B : U) -> ((_ : B) -> ((_ : B) -> (B)))
?24 : U = (B : U) -> ((_ : B) -> ((_ : B) -> (B)))
?25 : U = (B : U) -> ((_ : B) -> ((_ : B) -> (B)))
?26 : U = U
?27 : (A : U) -> ((B : (_ : A) -> (U)) -> (U)) = λx1. λx0. x1
?28 : (A : U) -> ((B : (_ : A) -> (U)) -> ((C : {a : A} -> ((_ : B(a)) -> (U))) -> (U))) = λx2. λx1. λx0. x2
?29 : (A : U) -> ((B : (_ : A) -> (U)) -> ((C : {a : A} -> ((_ : B(a)) -> (U))) -> ((a : A) -> ((b : B(a)) -> (A))))) = λx4. λx3. λx2. λx1. λx0. x1
?30 : (A : U) -> ((B : (_ : A) -> (U)) -> ((C : {a : A} -> ((_ : B(a)) -> (U))) -> ((f : {a : A} -> ((b : B(a)) -> (C{a}(b)))) -> ((g : (a : A) -> (B(a))) -> ((a : A) -> (A)))))) = λx5. λx4. λx3. λx2. λx1. λx0. x0
?31 : (A : U) -> ((B : (_ : A) -> (U)) -> ((C : {a : A} -> ((_ : B(a)) -> (U))) -> ((f : {a : A} -> ((b : B(a)) -> (C{a}(b)))) -> ((g : (a : A) -> (B(a))) -> ((a : A) -> (A)))))) = λx5. λx4. λx3. λx2. λx1. λx0. x0
?32 : U = (L : U) -> ((_ : (_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> ((_ : L) -> (L))) -> ((_ : L) -> (L)))
?33 : U = (L : U) -> ((_ : (_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> ((_ : L) -> (L))) -> ((_ : L) -> (L)))
?34 : (_ : (L : U) -> ((_ : (_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> ((_ : L) -> (L))) -> ((_ : L) -> (L)))) -> (U) = λx0. (L : U) -> ((_ : (_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> ((_ : L) -> (L))) -> ((_ : L) -> (L)))
?35 : {a : (L : U) -> ((_ : (_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> ((_ : L) -> (L))) -> ((_ : L) -> (L)))} -> ((_ : (L : U) -> ((_ : (_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> ((_ : L) -> (L))) -> ((_ : L) -> (L)))) -> (U)) = λ{x1}. λx0. (L : U) -> ((_ : (_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> ((_ : L) -> (L))) -> ((_ : L) -> (L)))
?36 : (a : (L : U) -> ((_ : (_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> ((_ : L) -> (L))) -> ((_ : L) -> (L)))) -> (U) = λx0. (B : U) -> ((_ : B) -> ((_ : B) -> (B)))
?37 : U = (B : U) -> ((_ : B) -> ((_ : B) -> (B)))
?38 : U = (B : U) -> ((_ : B) -> ((_ : B) -> (B)))
?39 : (a : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((b : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((N : U) -> ((s : (_ : N) -> (N)) -> ((z : N) -> (U))))) = λx4. λx3. λx2. λx1. λx0. x2
?40 : (a : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((b : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((N : U) -> ((s : (_ : N) -> (N)) -> ((z : N) -> (U))))) = λx4. λx3. λx2. λx1. λx0. x2
?41 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?42 : U = U
?43 : U = U
?44 : (A : U) -> ((x : A) -> (U)) = λx1. λx0. x1
?45 : U = U
?46 : (A : U) -> (U) = λx0. x0
?47 : (A : U) -> ((x : A) -> (U)) = λx1. λx0. x1
?48 : (A : U) -> ((x : A) -> ((y : A) -> ((_ : (P : (_ : A) -> (U)) -> ((_ : P(x)) -> (P(y)))) -> (U)))) = λx3. λx2. λx1. λx0. x3
?49 : (A : U) -> ((x : A) -> ((y : A) -> ((p : (P : (_ : A) -> (U)) -> ((_ : P(x)) -> (P(y)))) -> ((y : A) -> (U))))) = λx4. λx3. λx2. λx1. λx0. x4
?50 : (A : U) -> ((x : A) -> ((y : A) -> ((p : (P : (_ : A) -> (U)) -> ((_ : P(x)) -> (P(y)))) -> (U)))) = λx3. λx2. λx1. λx0. x3
?51 : (A : U) -> ((x : A) -> ((y : A) -> ((p : (P : (_ : A) -> (U)) -> ((_ : P(x)) -> (P(y)))) -> (A)))) = λx3. λx2. λx1. λx0. x2
?52 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?53 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?54 : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N))) = λN. λs. λz. s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
"""
    assertEquals(metaStr, expectedMetaStr)
    val termStr = term.read(ctx)
    val expectedTermStr = """let id : {A : U} -> ((_ : A) -> (A)) = λ{A}. λx. x;
let const : {A : ?0} -> ({B : ?1 A} -> ((_ : A) -> ((_ : B) -> (A)))) = λ{A}. λ{B}. λx. λy. x;
let group1 : {A : U} -> ({B : U} -> ((x : A) -> ((y : A) -> ((z : A) -> ((_ : B) -> (B)))))) = λ{A}. λ{B}. λx. λy. λz. λb. b;
let group2 : {A : ?2} -> ({B : ?3 A} -> ((x : A) -> ((y : A) -> ((z : A) -> ((_ : B) -> (B)))))) = λ{A}. λ{B}. λx. λy. λz. λb. b;
let the : (A : ?4) -> ((_ : A) -> (A)) = λ_. λx. x;
let argTest1 : ?5 = const{U}{U}(U);
let id2 : {A : ?6} -> ((_ : A) -> (A)) = λ{A}. λx. x;
let insert : {A : ?7} -> ((_ : A) -> (A)) = λ{A}. id{?8 A};
let noinsert : ?9 = λ{A}. λx. the(A)(x);
let insert2 : ?12 = λ{A}. λx. the(A)(x){?15}(U);
let Bool : U = (B : ?16) -> ((_ : B) -> ((_ : B) -> (B)));
let true : Bool = λB. λt. λf. t;
let false : Bool = λB. λt. λf. f;
let not : (_ : Bool) -> (Bool) = λb. λB. λt. λf. b(B)(f)(t);
let List : (_ : U) -> (U) = λA. (L : ?17 A) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> ((_ : L) -> (L)));
let nil : {A : ?18} -> (List(A)) = λ{A}. λL. λcons. λnil. nil;
let cons : {A : ?19} -> ((_ : A) -> ((_ : List(A)) -> (List(A)))) = λ{A}. λx. λxs. λL. λcons. λnil. cons(x)(xs(L)(cons)(nil));
let map : {A : ?20} -> ({B : ?21 A} -> ((_ : (_ : A) -> (B)) -> ((_ : List(A)) -> (List(B))))) = λ{A}. λ{B}. λf. λxs. λL. λc. λn. xs(L)(λa. c(f(a)))(n);
let list1 : List(Bool) = cons{?22}(true)(cons{?23}(false)(cons{?24}(true)(nil{?25})));
let comp : {A : ?26} -> ({B : (_ : A) -> (U)} -> ({C : {a : ?27 B A} -> ((_ : B(a)) -> (U))} -> ((f : {a : ?28 C B A} -> ((b : B(a)) -> (C{?29 b a C B A}(b)))) -> ((g : (a : A) -> (B(a))) -> ((a : A) -> (C{?30 a g f C B A}(g(a)))))))) = λ{A}. λ{B}. λ{C}. λf. λg. λa. f{?31 a g f C B A}(g(a));
let compExample : ?32 = comp{?33}{?34}{?35}(λ{a}. cons{?36 a}(true))(cons{?37}(false))(nil{?38});
let Nat : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)));
let mul : (_ : Nat) -> ((_ : Nat) -> (Nat)) = λa. λb. λN. λs. λz. a(?39 z s N b a)(b(?40 z s N b a)(s))(z);
let ten : Nat = λN. λs. λz. s(s(s(s(s(s(s(s(s(s(z))))))))));
let hundred : ?41 = mul(ten)(ten);
let Eq : {A : ?42} -> ((_ : A) -> ((_ : A) -> (U))) = λ{A}. λx. λy. (P : (_ : A) -> (U)) -> ((_ : P(x)) -> (P(y)));
let refl : {A : ?43} -> ({x : A} -> (Eq{?44 x A}(x)(x))) = λ{A}. λ{x}. λ_. λpx. px;
let sym : {A : ?45} -> ({x : ?46 A} -> ({y : ?47 x A} -> ((_ : Eq{A}(x)(y)) -> (Eq{?48 _ y x A}(y)(x))))) = λ{A}. λ{x}. λ{y}. λp. p(λy. Eq{?49 y p y x A}(y)(x))(refl{?50 p y x A}{?51 p y x A});
the(Eq{?52}(mul(ten)(ten))(hundred))(refl{?53}{?54})"""
    assertEquals(termStr, expectedTermStr)
  }

  test("prune.scope.prune") {
    import prune.scope._
    val raw = ScalaParser.parseInput("""
      let pr1 = λ f x. f x;
      let pr2 = λ f x y. f x y;
      let pr3 = λ f. f U;

      let pr4 = \f x. f x x x;
      let pr5 = \f g x. f (g x);

      U""")
    val ctx = Ctx.empty
    val (term, tty) = infer(ctx, raw)
    val metaStr = Meta.read
    val expectedMetaStr = """?0 : U = (f : (x : ?7) -> (?6(x))) -> ((x : ?7) -> (?6(x)))
?1 : U = (x : ?7) -> (?6(x))
?2 : (f : (x : ?7) -> (?6(x))) -> (U) = λf. ?7
?3 : (f : (x : ?7) -> (?6(x))) -> ((x : ?7) -> (U)) = λf. λx. ?7
?4 : (f : (x : ?7) -> (?6(x))) -> ((x : ?7) -> ((x : ?7) -> (U))) = λf. λx. λx. ?6(x)
?5 : U = ?7
?6 : (x : ?7) -> (U)
?7 : U
?8 : U = (f : (x : ?16) -> ((x : ?21(x)) -> (?20(x)(x)))) -> ((x : ?16) -> ((y : ?21(x)) -> (?20(x)(y))))
?9 : U = (x : ?16) -> ((x : ?21(x)) -> (?20(x)(x)))
?10 : (f : (x : ?16) -> ((x : ?21(x)) -> (?20(x)(x)))) -> (U) = λf. ?16
?11 : (f : (x : ?16) -> ((x : ?21(x)) -> (?20(x)(x)))) -> ((x : ?16) -> (U)) = λf. λx. ?21(x)
?12 : (f : (x : ?16) -> ((x : ?21(x)) -> (?20(x)(x)))) -> ((x : ?16) -> ((y : ?21(x)) -> (U))) = λf. λx. λy. ?16
?13 : (f : (x : ?16) -> ((x : ?21(x)) -> (?20(x)(x)))) -> ((x : ?16) -> ((y : ?21(x)) -> ((x : ?16) -> (U)))) = λf. λx. λy. λx. (x : ?21(x)) -> (?20(x)(x))
?14 : U = ?16
?15 : (x : ?16) -> (U) = λx0. (x : ?21(x0)) -> (?20(x0)(x))
?16 : U
?17 : (f : (x : ?16) -> ((x : ?21(x)) -> (?20(x)(x)))) -> ((x : ?16) -> ((y : ?21(x)) -> (U))) = λf. λx. λy. ?21(x)
?18 : (f : (x : ?16) -> ((x : ?21(x)) -> (?20(x)(x)))) -> ((x : ?16) -> ((y : ?21(x)) -> ((x : ?21(x)) -> (U)))) = λf. λx. λy. λx. ?20(x)(x)
?19 : (x : ?16) -> (U) = λx0. ?21(x0)
?20 : (x : ?16) -> ((x : ?21(x)) -> (U))
?21 : (x : ?16) -> (U)
?22 : U = (f : (x : U) -> (?27(x))) -> (?27(U))
?23 : U = (x : U) -> (?27(x))
?24 : (f : (x : U) -> (?27(x))) -> (U) = λf. U
?25 : (f : (x : U) -> (?27(x))) -> ((x : U) -> (U)) = λf. λx. ?27(x)
?26 : U = U
?27 : (x : U) -> (U)
?28 : U = (f : (x : ?35) -> ((x : ?35) -> ((x : ?35) -> (?43(x)(x))))) -> ((x : ?35) -> (?43(x)(x)))
?29 : U = (x : ?35) -> ((x : ?35) -> ((x : ?35) -> (?43(x)(x))))
?30 : (f : (x : ?35) -> ((x : ?35) -> ((x : ?35) -> (?43(x)(x))))) -> (U) = λf. ?35
?31 : (f : (x : ?35) -> ((x : ?35) -> ((x : ?35) -> (?43(x)(x))))) -> ((x : ?35) -> (U)) = λf. λx. ?35
?32 : (f : (x : ?35) -> ((x : ?35) -> ((x : ?35) -> (?43(x)(x))))) -> ((x : ?35) -> ((x : ?35) -> (U))) = λf. λx. λx. (x : ?35) -> ((x : ?35) -> (?43(x)(x)))
?33 : U = ?35
?34 : (x : ?35) -> (U) = λx0. (x : ?35) -> ((x : ?35) -> (?43(x)(x)))
?35 : U
?36 : (f : (x : ?35) -> ((x : ?35) -> ((x : ?35) -> (?43(x)(x))))) -> ((x : ?35) -> (U)) = λf. λx. ?35
?37 : (f : (x : ?35) -> ((x : ?35) -> ((x : ?35) -> (?43(x)(x))))) -> ((x : ?35) -> ((x : ?35) -> (U))) = λf. λx. λx. (x : ?35) -> (?43(x)(x))
?38 : (x : ?35) -> (U) = λx0. ?35
?39 : (x : ?35) -> ((x : ?35) -> (U)) = λx1. λx0. (x : ?35) -> (?43(x0)(x))
?40 : (f : (x : ?35) -> ((x : ?35) -> ((x : ?35) -> (?43(x)(x))))) -> ((x : ?35) -> (U)) = λf. λx. ?35
?41 : (f : (x : ?35) -> ((x : ?35) -> ((x : ?35) -> (?43(x)(x))))) -> ((x : ?35) -> ((x : ?35) -> (U))) = λf. λx. λx. ?43(x)(x)
?42 : (x : ?35) -> (U) = λx0. ?35
?43 : (x : ?35) -> ((x : ?35) -> (U))
?44 : U = (f : (x : ?57) -> (?51(x))) -> ((g : (x : ?56(f)) -> (?57)) -> ((x : ?56(f)) -> (?51(g(x)))))
?45 : U = (x : ?57) -> (?51(x))
?46 : (f : (x : ?57) -> (?51(x))) -> (U) = λx0. (x : ?56(x0)) -> (?57)
?47 : (f : (x : ?57) -> (?51(x))) -> ((g : (x : ?56(f)) -> (?57)) -> (U)) = λf. λg. ?56(f)
?48 : (f : (x : ?57) -> (?51(x))) -> ((g : (x : ?56(f)) -> (?57)) -> ((x : ?56(f)) -> (U))) = λf. λg. λx. ?57
?49 : (f : (x : ?57) -> (?51(x))) -> ((g : (x : ?56(f)) -> (?57)) -> ((x : ?56(f)) -> ((x : ?57) -> (U)))) = λf. λg. λx. λx. ?51(x)
?50 : U = ?57
?51 : (x : ?57) -> (U)
?52 : (f : (x : ?57) -> (?51(x))) -> ((g : (x : ?56(f)) -> (?57)) -> ((x : ?56(f)) -> (U))) = λf. λg. λx. ?56(f)
?53 : (f : (x : ?57) -> (?51(x))) -> ((g : (x : ?56(f)) -> (?57)) -> ((x : ?56(f)) -> ((x : ?56(f)) -> (U)))) = λf. λg. λx. λx. ?57
?54 : (f : (x : ?57) -> (?51(x))) -> (U) = λx0. ?56(x0)
?55 : (f : (x : ?57) -> (?51(x))) -> ((x : ?56(f)) -> (U)) = λf. λx. ?57
?56 : (f : (x : ?57) -> (?51(x))) -> (U)
?57 : U
"""
    assertEquals(metaStr, expectedMetaStr)
    val termStr = term.read(ctx)
    val expectedTermStr = """let pr1 : ?0 = λf. λx. f(x);
let pr2 : ?8 = λf. λx. λy. f(x)(y);
let pr3 : ?22 = λf. f(U);
let pr4 : ?28 = λf. λx. f(x)(x)(x);
let pr5 : ?44 = λf. λg. λx. f(g(x));
U"""
    assertEquals(termStr, expectedTermStr)
  }

  test("prune.nonlinear.nonlinear") {
    import prune.nonlinear._
    val raw = ScalaParser.parseInput("""
    -- we use Eq to test unification

    let Eq : {A : U} → A → A → U
        = λ {A} x y. (P : A → U) → P x → P y;
    let refl : {A : U}{x : A} → Eq {A} x x
        = λ _ px. px;
    
    -- inline type annotation
    let the : (A : U) → A → A = λ _ x. x;

    let m : (A : U)(B : U) → U → U → U = _;
    let test = λ a b. the (Eq (m a a) (λ x y. y)) refl;
    U
    """)
    val ctx = Ctx.empty
    val (term, tty) = infer(ctx, raw)
    val metaStr = Meta.read
    val expectedMetaStr = """?0 : (A : U) -> ((B : U) -> ((_ : U) -> ((_ : U) -> (U)))) = λA. λB. λx. λy. y
?1 : U = (a : U) -> ((b : ?3(a)) -> ((P : (_ : (_ : U) -> ((_ : U) -> (U))) -> (U)) -> ((_ : P(λx. λy. y)) -> (P(λx. λy. y)))))
?2 : U = U
?3 : (a : U) -> (U)
?4 : (a : U) -> ((b : ?3(a)) -> (U)) = λa. λb. (_ : U) -> ((_ : U) -> (U))
?5 : (a : U) -> ((b : ?3(a)) -> (U)) = λa. λb. (_ : U) -> ((_ : U) -> (U))
?6 : (a : U) -> ((b : ?3(a)) -> ((_ : U) -> ((_ : U) -> (U)))) = λa. λb. λx. λy. y
?7 : (_ : U) -> ((_ : U) -> (U)) = λx. λy. y
"""
    assertEquals(metaStr, expectedMetaStr)
    val termStr = term.read(ctx)
    val expectedTermStr =
      """let Eq : {A : U} -> ((_ : A) -> ((_ : A) -> (U))) = λ{A}. λx. λy. (P : (_ : A) -> (U)) -> ((_ : P(x)) -> (P(y)));
let refl : {A : U} -> ({x : A} -> (Eq{A}(x)(x))) = λ{A}. λ{x}. λ_. λpx. px;
let the : (A : U) -> ((_ : A) -> (A)) = λ_. λx. x;
let m : (A : U) -> ((B : U) -> ((_ : U) -> ((_ : U) -> (U)))) = ?0;
let test : ?1 = λa. λb. the(Eq{?4 b a}(m(a)(a))(λx. λy. y))(refl{?5 b a}{?6 b a});
U"""
    assertEquals(termStr, expectedTermStr)
  }

  test("prune.nonlinear.unsolvable") {
    import prune.nonlinear._
    Meta.init()
    val raw = ScalaParser.parseInput("""
    -- we use Eq to test unification

    let Eq : {A : U} → A → A → U
        = λ {A} x y. (P : A → U) → P x → P y;
    let refl : {A : U}{x : A} → Eq {A} x x
        = λ _ px. px;
    
    -- inline type annotation
    let the : (A : U) → A → A = λ _ x. x;

    let m : (A : U)(B : U) → A → B → B = _;
    let test = λ a b. the (Eq (m a a) (λ x y. y)) refl;
    U
    """)
    val ctx = Ctx.empty
    val expectedMsg = """At Line 13 Column 51:
    let test = λ a b. the (Eq (m a a) (λ x y. y)) refl;
                                                  ^
When checking or inferring refl:

Can't unify '(P : (_ : (_ : a) -> ((_ : a) -> (a))) -> (U)) -> ((_ : P(?0(a)(a))) -> (P(λx. λy. y)))' and '(P : (_ : (_ : a) -> ((_ : a) -> (a))) -> (U)) -> ((_ : P(?6(a)(b))) -> (P(?6(a)(b))))':

Variable out of scope when solving meta"""
    var msg = ""
    try infer(ctx, raw)
    catch case e => msg = e.getMessage()
    assertEquals(msg, expectedMsg)
  }

  test("prune.nonlinear.intersect") {
    import prune.nonlinear._
    Meta.init()
    val raw = ScalaParser.parseInput("""
    -- we use Eq to test unification

    let Eq : {A : U} → A → A → U
        = λ {A} x y. (P : A → U) → P x → P y;
    let refl : {A : U}{x : A} → Eq {A} x x
        = λ _ px. px;
    
    -- inline type annotation
    let the : (A : U) → A → A = λ _ x. x;

    let m : U → U → U → U = _;
    let test = λ a b c. the (Eq (m a b c) (m c b a)) refl;
    U
    """)
    val ctx = Ctx.empty
    val expectedMsg = """At Line 13 Column 54:
    let test = λ a b c. the (Eq (m a b c) (m c b a)) refl;
                                                     ^
When checking or inferring refl:

Can't unify '(P : (_ : U) -> (U)) -> ((_ : P(?7(a)(b)(c))) -> (P(?7(c)(b)(a))))' and '(P : (_ : U) -> (U)) -> ((_ : P(?7(a)(b)(c))) -> (P(?7(a)(b)(c))))':

Values obviously inconsistent"""
    var msg = ""
    try infer(ctx, raw)
    catch case e => msg = e.getMessage()
    assertEquals(msg, expectedMsg)
  }
}
