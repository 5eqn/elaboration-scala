// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class ImplicitTest extends munit.FunSuite {
  test("implicit.modularize.solve") {
    import `implicit`.modularize._
    val raw = ScalaParser.parseInput("""
    let id : (A : _) -> A -> A
      = \A x. x;
    
    let List : U -> U
      = \A. (L : _) -> (A -> L -> L) -> L -> L;
    
    let nil : (A : _) -> List A
      = \A L cons nil. nil;
    
    let cons : (A : _) -> A -> List A -> List A
      = \A x xs L cons nil. cons x (xs _ cons nil);
    
    let Bool : U
      = (B : _) -> B -> B -> B;
    
    let true : Bool
      = \B t f. t;
    
    let false : Bool
      = \B t f. f;
    
    let not : Bool -> Bool
      = \b B t f. b B f t;
    
    let list1 : List Bool
      = cons _ (id _ true) (nil _);
    
    let Eq : (A : _) -> A -> A -> U
      = \A x y. (P : A -> U) -> P x -> P y;
    
    let refl : (A : _)(x : A) -> Eq A x x
      = \A x P px. px;
    
    let list1 : List Bool
      = cons _ true (cons _ false (nil _));
    
    let Nat  : U = (N : U) -> (N -> N) -> N -> N;
    let five : Nat = \N s z. s (s (s (s (s z))));
    let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
    let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;
    
    let ten      : Nat = add five five;
    let hundred  : Nat = mul ten ten;
    let thousand : Nat = mul ten hundred;
    
    let eqTest : Eq _ hundred hundred = refl _ _;
    
    U""")
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("implicit.model.solve") {
    import `implicit`.model._
    val raw = ScalaParser.parseInput("""
    let id : (A : _) -> A -> A
      = \A x. x;
    
    let List : U -> U
      = \A. (L : _) -> (A -> L -> L) -> L -> L;
    
    let nil : (A : _) -> List A
      = \A L cons nil. nil;
    
    let cons : (A : _) -> A -> List A -> List A
      = \A x xs L cons nil. cons x (xs _ cons nil);
    
    let Bool : U
      = (B : _) -> B -> B -> B;
    
    let true : Bool
      = \B t f. t;
    
    let false : Bool
      = \B t f. f;
    
    let not : Bool -> Bool
      = \b B t f. b B f t;
    
    let list1 : List Bool
      = cons _ (id _ true) (nil _);
    
    let Eq : (A : _) -> A -> A -> U
      = \A x y. (P : A -> U) -> P x -> P y;
    
    let refl : (A : _)(x : A) -> Eq A x x
      = \A x P px. px;
    
    let list1 : List Bool
      = cons _ true (cons _ false (nil _));
    
    let Nat  : U = (N : U) -> (N -> N) -> N -> N;
    let five : Nat = \N s z. s (s (s (s (s z))));
    let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
    let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;
    
    let ten      : Nat = add five five;
    let hundred  : Nat = mul ten ten;
    let thousand : Nat = mul ten hundred;
    
    let eqTest : Eq _ hundred hundred = refl _ _;
    
    U""")
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("implicit.insert.solve") {
    import `implicit`.model._
    val raw = ScalaParser.parseInput("""
    let id : (A : _) -> A -> A
      = \A x. x;
    
    let List : U -> U
      = \A. (L : _) -> (A -> L -> L) -> L -> L;
    
    let nil : (A : _) -> List A
      = \A L cons nil. nil;
    
    let cons : (A : _) -> A -> List A -> List A
      = \A x xs L cons nil. cons x (xs _ cons nil);
    
    let Bool : U
      = (B : _) -> B -> B -> B;
    
    let true : Bool
      = \B t f. t;
    
    let false : Bool
      = \B t f. f;
    
    let not : Bool -> Bool
      = \b B t f. b B f t;
    
    let list1 : List Bool
      = cons _ (id _ true) (nil _);
    
    let Eq : (A : _) -> A -> A -> U
      = \A x y. (P : A -> U) -> P x -> P y;
    
    let refl : (A : _)(x : A) -> Eq A x x
      = \A x P px. px;
    
    let list1 : List Bool
      = cons _ true (cons _ false (nil _));
    
    let Nat  : U = (N : U) -> (N -> N) -> N -> N;
    let five : Nat = \N s z. s (s (s (s (s z))));
    let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
    let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;
    
    let ten      : Nat = add five five;
    let hundred  : Nat = mul ten ten;
    let thousand : Nat = mul ten hundred;
    
    let eqTest : Eq _ hundred hundred = refl _ _;
    
    U""")
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("implicit.insert.working") {
    import `implicit`.insert._
    val raw = ScalaParser.parseInput("""
    -- bracketed args are implicit, elaboration inserts implicit lambdas for them (if they're not
    -- already present)
    let id : {A : U} -> A -> A = \x. x;   -- elaborated to \{A} x. x
    
    -- implicit arg types can be omitted
    let const : {A B} -> A -> B -> A = \x y. x;
    
    -- function arguments can be grouped:
    let group1 : {A B : U}(x y z : A) -> B -> B = \x y z b. b;
    let group2 : {A B}(x y z : A) -> B -> B = \x y z b. b;
    
    -- explicit id function used for annotation as in Idris
    let the : (A : _) -> A -> A = \_ x. x;
    
    -- implicit args can be explicitly given
    let argTest1 = const {U}{U} U;
    
    -- TODO or can be given by name (names come from the function types)
    -- let argTest2 = const {B = U} U;  -- only give B, the second implicit arg
    
    -- likewise, implicit lambdas can be explicitly given
    let id2 : {A} -> A -> A = \{A} x. x;
    
    -- TODO we can also bind only some implicit args, using named implicit lambdas
    -- let namedLam  : {A B C} -> A -> B -> C -> A = \{B = B} a b c. a; -- second arg in scope as B
    -- let namedLam2 : {A B C} -> A -> B -> C -> A = \{B = X} a b c. a; -- second arg in scope as X
    -- let namedLam2 : {A B C} -> A -> B -> C -> A = \{C = X} a b c. a; -- third arg in scope as X
    
    -- Here the output rhs is \{A}. id {A}. First, we insert \{A}, then we apply id to {?n},
    -- and ?n is solved to A a bit later.
    let insert : {A} -> A -> A = id;
    
    -- Here we don't insert, because rhs is already an implicit lambda.
    let noinsert = \{A} x. the A x;
    
    -- Here we insert, because although we already have an implicit lambda, it is applied
    -- explicitly to something.
    let insert2 = (\{A} x. the A x) U;  -- (\{A} x. the A x) {U} U
    
    
    --------------------------------------------------------------------------------
    
    -- bool
    let Bool : U
        = (B : _) -> B -> B -> B;
    let true : Bool
        = \B t f. t;
    let false : Bool
        = \B t f. f;
    let not : Bool -> Bool
        = \b B t f. b B f t;
    
    -- lists
    let List : U -> U
        = \A. (L : _) -> (A -> L -> L) -> L -> L;
    let nil : {A} -> List A
        = \L cons nil. nil;
    let cons : {A} -> A -> List A -> List A
        = \x xs L cons nil. cons x (xs L cons nil);
    let map : {A B} -> (A -> B) -> List A -> List B
        = \{A}{B} f xs L c n. xs L (\a. c (f a)) n;
    let list1 : List Bool
        = cons true (cons false (cons true nil));
    
    -- dependent function composition
    let comp : {A}{B : A -> U}{C : {a} -> B a -> U}
               (f : {a}(b : B a) -> C b)
               (g : (a : A) -> B a)
               (a : A)
               -> C (g a)
        = \f g a. f (g a);
    
    let compExample = comp (cons true) (cons false) nil;
    
    -- nat
    let Nat : U
        = (N : U) -> (N -> N) -> N -> N;
    let mul : Nat -> Nat -> Nat
        = \a b N s z. a _ (b _ s) z;
    let ten : Nat
        = \N s z. s (s (s (s (s (s (s (s (s (s z)))))))));
    let hundred = mul ten ten;
    
    -- Leibniz equality
    let Eq : {A} -> A -> A -> U
        = \{A} x y. (P : A -> U) -> P x -> P y;
    let refl : {A}{x : A} -> Eq x x
        = \_ px. px;
    
    let sym : {A x y} → Eq {A} x y → Eq y x
      = λ {A}{x}{y} p. p (λ y. Eq y x) refl;
    
    the (Eq (mul ten ten) hundred) refl
    """)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }

  test("implicit.named.working") {
    import `implicit`.named._
    val raw = ScalaParser.parseInput("""
    -- bracketed args are implicit, elaboration inserts implicit lambdas for them (if they're not
    -- already present)
    let id : {A : U} -> A -> A = \x. x;   -- elaborated to \{A} x. x
    
    -- implicit arg types can be omitted
    let const : {A B} -> A -> B -> A = \x y. x;
    
    -- function arguments can be grouped:
    let group1 : {A B : U}(x y z : A) -> B -> B = \x y z b. b;
    let group2 : {A B}(x y z : A) -> B -> B = \x y z b. b;
    
    -- explicit id function used for annotation as in Idris
    let the : (A : _) -> A -> A = \_ x. x;
    
    -- implicit args can be explicitly given
    let argTest1 = const {U}{U} U;
    
    -- or can be given by name (names come from the function types)
    let argTest2 = const {B = U} U;  -- only give B, the second implicit arg
    
    -- likewise, implicit lambdas can be explicitly given
    let id2 : {A} -> A -> A = \{A} x. x;
    
    -- we can also bind only some implicit args, using named implicit lambdas
    let namedLam  : {A B C} -> A -> B -> C -> A = \{B = B} a b c. a; -- second arg in scope as B
    let namedLam2 : {A B C} -> A -> B -> C -> A = \{B = X} a b c. a; -- second arg in scope as X
    let namedLam2 : {A B C} -> A -> B -> C -> A = \{C = X} a b c. a; -- third arg in scope as X
    
    -- Here the output rhs is \{A}. id {A}. First, we insert \{A}, then we apply id to {?n},
    -- and ?n is solved to A a bit later.
    let insert : {A} -> A -> A = id;
    
    -- Here we don't insert, because rhs is already an implicit lambda.
    let noinsert = \{A} x. the A x;
    
    -- Here we insert, because although we already have an implicit lambda, it is applied
    -- explicitly to something.
    let insert2 = (\{A} x. the A x) U;  -- (\{A} x. the A x) {U} U
    
    
    --------------------------------------------------------------------------------
    
    -- bool
    let Bool : U
        = (B : _) -> B -> B -> B;
    let true : Bool
        = \B t f. t;
    let false : Bool
        = \B t f. f;
    let not : Bool -> Bool
        = \b B t f. b B f t;
    
    -- lists
    let List : U -> U
        = \A. (L : _) -> (A -> L -> L) -> L -> L;
    let nil : {A} -> List A
        = \L cons nil. nil;
    let cons : {A} -> A -> List A -> List A
        = \x xs L cons nil. cons x (xs L cons nil);
    let map : {A B} -> (A -> B) -> List A -> List B
        = \{A}{B} f xs L c n. xs L (\a. c (f a)) n;
    let list1 : List Bool
        = cons true (cons false (cons true nil));
    
    -- dependent function composition
    let comp : {A}{B : A -> U}{C : {a} -> B a -> U}
               (f : {a}(b : B a) -> C b)
               (g : (a : A) -> B a)
               (a : A)
               -> C (g a)
        = \f g a. f (g a);
    
    let compExample = comp (cons true) (cons false) nil;
    
    -- nat
    let Nat : U
        = (N : U) -> (N -> N) -> N -> N;
    let mul : Nat -> Nat -> Nat
        = \a b N s z. a _ (b _ s) z;
    let ten : Nat
        = \N s z. s (s (s (s (s (s (s (s (s (s z)))))))));
    let hundred = mul ten ten;
    
    -- Leibniz equality
    let Eq : {A} -> A -> A -> U
        = \{A} x y. (P : A -> U) -> P x -> P y;
    let refl : {A}{x : A} -> Eq x x
        = \_ px. px;
    
    let sym : {A x y} → Eq {A} x y → Eq y x
      = λ {A}{x}{y} p. p (λ y. Eq y x) refl;
    
    the (Eq (mul ten ten) hundred) refl
    """)
    val ctx = Ctx.empty
    val term = infer(ctx, raw)
  }
}
