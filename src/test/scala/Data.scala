val solveTest = """
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

U"""

val insertTest = """
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
"""

val fcpolyFullTest = """
-- Preliminary defs
------------------------------------------------------------

let List   : U → U                             = λ A. (L : U) → L → (A → L → L) → L;
let nil    : {A} → List A                      = λ L n c. n;
let cons   : {A} → A → List A → List A         = λ a as L n c. c a (as L n c);
let Bool   : U                                 = (B : U) → B → B → B;
let true   : Bool                              = λ b t f. t;
let Pair   : U → U → U                         = λ A B. (P : U) → (A → B → P) → P;
let pair   : {A B} → A → B → Pair A B          = λ a b P p. p a b;
let Nat    : U                                 = (N : U) → (N → N) → N → N;
let zero   : Nat                               = λ N s z. z;
let suc    : Nat → Nat                         = λ n N s z. s (n N s z);
let append : {A} → List A → List A → List A    = λ xs ys L n c. xs L (ys L n c) c;
let length : {A} → List A → Nat                = λ as N s z. as N z (λ x. s);
let map    : {A B} → (A → B) → List A → List B = λ f as L n c. as L n (λ a. c (f a));
let ST     : U → U → U                         = λ S A. S → A;
let runST  : {A} → ({S} → ST S A) → A          = λ f. f {Bool} true;
let argST  : {S} → ST S Nat                    = λ _. zero;
let Id     : U → U                             = λ A. (I : U) → (A → I) → I;
let mkId   : {A} → A → Id A                    = λ a I f. f a;
let unId   : {A} → Id A → A                    = λ i. i _ (λ x. x);
let the    : (A : U) → A → A                   = λ A a. a;
let const  : {A B} → A → B → A                 = λ x y. x;
let IdTy   : U                                 = {A} → A → A;
let single : {A} → A → List A                  = λ a. cons a nil;
let id     : {A} → A → A                       = λ a. a;
let ids    : List IdTy                         = nil;
let oneId  : Id IdTy                           = mkId id;
let app    : {A B} → (A → B) → A → B           = id;
let revapp : {A B} → A → (A → B) → B           = λ x f. f x;
let poly   : IdTy → Pair Nat Bool              = λ f. pair (f zero) (f true);
let choose : {A} → A → A → A                   = const;
let auto   : IdTy → IdTy                       = id;
let auto2  : {B} → IdTy → B → B                = λ _ b. b;


-- A: polymorphic instantiation
--------------------------------------------------------------------------------

let A1 = λ x y. y;

let A2 : IdTy → IdTy = choose id;

let A3 = choose nil ids;

let A4 : IdTy → IdTy = λ (x : IdTy). x x;

let A5 = id auto;

let A6 : {B} → IdTy → B → B = id auto2;

let A7 = choose id auto;

-- let A8 = choose id auto2 in -- FAILS the reason is simply that the types are
--   definitionally different, the orders of implicit args do not match. We
--   do *not* reorder or float out implicit args, intentionally, since we
--   support mixing implicit and explicit args in arbitrary order.

let A9 : ({A} → (A → A) → List A → A) → IdTy
    = λ f. f (choose id) ids;

let A10 = poly id;

let A11 = poly (λ x. x);

let A12 = id poly (λ x. x);

-- B: inference of polymorphic arguments
--------------------------------------------------------------------------------

-- FAILS
-- let B1 = λ f. pair (f zero) (f true);

-- FAILS
-- let B2 = λ x. poly (unId x);

-- C: functions on polymorphic lists
--------------------------------------------------------------------------------

let C1 = length ids;

let C2 = id ids;

let C3 : IdTy = unId oneId;

let C4 : List IdTy = single id;

let C5 = cons id ids;

let C6 = cons (λ x. x) ids;

let C7 = append (single suc) (single id);

let C8 : _ → IdTy = λ (g : {A} → List A → List A → A). g (single id) ids;

let C9 = map poly (single id);

let C10 = map unId (single oneId);

-- D: application functions
--------------------------------------------------------------------------------

let D1 = app poly id;

let D2 = revapp id poly;

let D3 = runST argST;

let D4 = app runST argST;

let D5 = revapp argST runST;

-- -- E: η-expansion
-- --------------------------------------------------------------------------------

-- let E1 =   -- FAILS
--   λ (h : Nat → {A} → A → A)(k : {A} → A → List A → A)(lst : List ({A} → Nat → A → A)).
--   k h lst;
--   -- fails again because of mismatched implicit/explicit arguments

let E2 =
  λ (h : Nat → {A} → A → A)(k : {A} → A → List A → A)(lst : List ({A} → Nat → A → A)).
  k (λ x. h x) lst;

let E3 =
  λ (r : ({A} → A → {B} → B → B) → Nat). r (λ x y. y);

U
"""

val fcpolyFullMeta = """?0 : U = U
?1 : U = U
?2 : U = U
?3 : (A : U) -> (U) = λA. U
?4 : U = U
?5 : U = U
?6 : U = U
?7 : (A : U) -> (U) = λA. U
?8 : U = U
?9 : (A : U) -> (U) = λA. U
?10 : U = U
?11 : U = U
?12 : U = U
?13 : (A : U) -> ((i : (I : U) -> ((_ : (_ : A) -> (I)) -> (I))) -> (U)) = λA. λi. A
?14 : (A : U) -> ((i : (I : U) -> ((_ : (_ : A) -> (I)) -> (I))) -> ((x : A) -> (A))) = λA. λi. λx. x
?15 : U = U
?16 : (A : U) -> (U) = λA. U
?17 : U = U
?18 : U = U
?19 : (A : U) -> ((a : A) -> (U)) = λA. λa. A
?20 : (A : U) -> ((a : A) -> (A)) = λA. λa. a
?21 : (A : U) -> ((a : A) -> (U)) = λA. λa. A
?22 : U = U
?23 : U = {A : U} -> ((_ : A) -> (A))
?24 : U = {A : U} -> ((_ : A) -> (A))
?25 : {A : U} -> ((_ : A) -> (A)) = λ{A}. λa. a
?26 : (A : U) -> (U) = λA. A
?27 : U = U
?28 : (A : U) -> (U) = λA. U
?29 : (A : U) -> ((B : U) -> (U)) = λA. λB. (_ : A) -> (B)
?30 : U = U
?31 : (A : U) -> (U) = λA. U
?32 : (f : {A : U} -> ((_ : A) -> (A))) -> (U) = λf. (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?33 : (f : {A : U} -> ((_ : A) -> (A))) -> (U) = λf. (B : U) -> ((_ : B) -> ((_ : B) -> (B)))
?34 : (f : {A : U} -> ((_ : A) -> (A))) -> ((N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) = λf. f{(N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))}(λN. λs. λz. z)
?35 : (f : {A : U} -> ((_ : A) -> (A))) -> ((B : U) -> ((_ : B) -> ((_ : B) -> (B)))) = λf. f{(B : U) -> ((_ : B) -> ((_ : B) -> (B)))}(λb. λt. λf. t)
?36 : (f : {A : U} -> ((_ : A) -> (A))) -> (U) = λf. (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?37 : (f : {A : U} -> ((_ : A) -> (A))) -> ((N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) = λf. λN. λs. λz. z
?38 : (f : {A : U} -> ((_ : A) -> (A))) -> (U) = λf. (B : U) -> ((_ : B) -> ((_ : B) -> (B)))
?39 : (f : {A : U} -> ((_ : A) -> (A))) -> ((B : U) -> ((_ : B) -> ((_ : B) -> (B)))) = λf. λb. λt. λf. t
?40 : U = U
?41 : (A : U) -> (U) = λA. A
?42 : (A : U) -> (U) = λA. A
?43 : U = {A : U} -> ((_ : A) -> (A))
?44 : U = U
?45 : U = (x : ?122) -> ((y : ?123(x)) -> (?123(x)))
?46 : (x : ?122) -> ((y : ?123(x)) -> (?123(x))) = λx. λy. y
?47 : U = {A : U} -> ((_ : A) -> (A))
?48 : {A : U} -> ((_ : A) -> (A)) = λ{A}. λa. a
?49 : (A : U) -> (U) = λA. A
?50 : U
?51 : ?50 = ?117
?52 : (x : {A : U} -> ((_ : A) -> (A))) -> ((A : U) -> (U)) = λx. λA. (_ : A) -> (A)
?53 : (x : {A : U} -> ((_ : A) -> (A))) -> ((A : U) -> ((_ : A) -> (A))) = λx. λA. x{A}
?54 : (x : {A : U} -> ((_ : A) -> (A))) -> ((A : U) -> (U)) = λx. λA. A
?55 : U
?56 : ?55 = ?126
?57 : U = U
?58 : (B : U) -> (U) = λB. (_ : {A : U} -> ((_ : A) -> (A))) -> ((_ : B) -> (B))
?59 : (B : U) -> ((_ : {A : U} -> ((_ : A) -> (A))) -> ((_ : B) -> (B))) = λB. λ_. λb. b
?60 : (B : U) -> (U) = λB. B
?61 : U
?62 : ?61 = ?120
?63 : U = U
?64 : (f : {A : U} -> ((_ : (_ : A) -> (A)) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((A : U) -> (U)) = λf. λA. {A : U} -> ((_ : A) -> (A))
?65 : (f : {A : U} -> ((_ : (_ : A) -> (A)) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((A : U) -> (U)) = λf. λA. {A : U} -> ((_ : A) -> (A))
?66 : (f : {A : U} -> ((_ : (_ : A) -> (A)) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((A : U) -> ({A : U} -> ((_ : A) -> (A)))) = λf. λA. λ{A}. λa. a
?67 : (f : {A : U} -> ((_ : (_ : A) -> (A)) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((A : U) -> (U)) = λf. λA. {A : U} -> ((_ : A) -> (A))
?68 : (f : {A : U} -> ((_ : (_ : A) -> (A)) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((A : U) -> ((A : U) -> (U))) = λf. λA. λA. A
?69 : (f : {A : U} -> ((_ : (_ : A) -> (A)) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((A : U) -> (U)) = λf. λA. A
?70 : U = (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))
?71 : (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P)) = λP. λp. p(λN. λs. λz. z)(λb. λt. λf. t)
?72 : U = (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))
?73 : (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P)) = λP. λp. p(λN. λs. λz. z)(λb. λt. λf. t)
?74 : U = (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))
?75 : (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P)) = λP. λp. p(λN. λs. λz. z)(λb. λt. λf. t)
?76 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?77 : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N))) = λN. λs. λz. z
?78 : U
?79 : ?78 = ?180
?80 : (A : U) -> (U) = λA. {A : U} -> ((_ : A) -> (A))
?81 : (A : U) -> (U) = λA. A
?82 : U = {A : U} -> ((_ : A) -> (A))
?83 : {A : U} -> ((_ : A) -> (A)) = λ{A}. λa. a
?84 : (A : U) -> (U) = λA. A
?85 : U = (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : A) -> (A))) -> ((_ : L) -> (L))) -> (L)))
?86 : (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : A) -> (A))) -> ((_ : L) -> (L))) -> (L))) = λL. λn. λc. c(λ{A}. λa. a)(n)
?87 : U = (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : A) -> (A))) -> ((_ : L) -> (L))) -> (L)))
?88 : (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : A) -> (A))) -> ((_ : L) -> (L))) -> (L))) = λL. λn. λc. c(λ{A}. λx. x)(n)
?89 : U = (L : U) -> ((_ : L) -> ((_ : (_ : ?170) -> ((_ : L) -> (L))) -> (L)))
?90 : (L : U) -> ((_ : L) -> ((_ : (_ : ?170) -> ((_ : L) -> (L))) -> (L))) = λL. λn. λc. c(?172)(c(?174)(n))
?91 : U = {A : U} -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))
?92 : U = U
?93 : (g : {A : U} -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((A : U) -> (U)) = λg. λA. {A : U} -> ((_ : A) -> (A))
?94 : (g : {A : U} -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((A : U) -> (U)) = λg. λA. {A : U} -> ((_ : A) -> (A))
?95 : (g : {A : U} -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((A : U) -> ({A : U} -> ((_ : A) -> (A)))) = λg. λA. λ{A}. λa. a
?96 : (g : {A : U} -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((A : U) -> ((A : U) -> (U))) = λg. λA. λA. A
?97 : (g : {A : U} -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((A : U) -> (U)) = λg. λA. A
?98 : U = (L : U) -> ((_ : L) -> ((_ : (_ : (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))) -> ((_ : L) -> (L))) -> (L)))
?99 : (L : U) -> ((_ : L) -> ((_ : (_ : (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))) -> ((_ : L) -> (L))) -> (L))) = λL. λn. λc. c(λP. λp. p(λN. λs. λz. z)(λb. λt. λf. t))(n)
?100 : U = (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : A) -> (A))) -> ((_ : L) -> (L))) -> (L)))
?101 : (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : A) -> (A))) -> ((_ : L) -> (L))) -> (L))) = λL. λn. λc. c(λ{A}. λa. a)(n)
?102 : U = (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))
?103 : (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P)) = λP. λp. p(λN. λs. λz. z)(λb. λt. λf. t)
?104 : U = (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))
?105 : (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P)) = λP. λp. p(λN. λs. λz. z)(λb. λt. λf. t)
?106 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?107 : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N))) = λN. λs. λz. z
?108 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?109 : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N))) = λN. λs. λz. z
?110 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?111 : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N))) = λN. λs. λz. z
?112 : U = (h : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ({A : U} -> ((_ : A) -> (A)))) -> ((k : {A : U} -> ((_ : A) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((lst : (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : A) -> (A)))) -> ((_ : L) -> (L))) -> (L)))) -> ((_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : ?150(h)(k)(lst)) -> (?150(h)(k)(lst))))))
?113 : (h : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ({A : U} -> ((_ : A) -> (A)))) -> ((k : {A : U} -> ((_ : A) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((lst : (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : A) -> (A)))) -> ((_ : L) -> (L))) -> (L)))) -> ((_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : ?150(h)(k)(lst)) -> (?150(h)(k)(lst)))))) = λh. λk. λlst. k{{A : U} -> ((_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : A) -> (A)))}(λ{A}. λx. h(x){A})(lst){?150(h)(k)(lst)}
?114 : U = (r : (_ : {A : U} -> ((_ : A) -> ({B : U} -> ((_ : B) -> (B))))) -> ((N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N))))) -> ((N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N))))
?115 : (r : (_ : {A : U} -> ((_ : A) -> ({B : U} -> ((_ : B) -> (B))))) -> ((N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N))))) -> ((N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) = λr. r(λ{A}. λx. λ{B}. λy. y)
?116 : U = ?50
?117 : ?50
?118 : ?50
?119 : U = ?61
?120 : ?61
?121 : ?61
?122 : U
?123 : (x : ?122) -> (U)
?124 : U = {A : U} -> ((_ : A) -> (A))
?125 : U = ?55
?126 : ?55
?127 : (A : U) -> (U) = λA. A
?128 : U = {A : U} -> ((_ : A) -> (A))
?129 : U = (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))
?130 : U = {A : U} -> ((_ : A) -> (A))
?131 : {A : U} -> ((_ : A) -> (A)) = λ{A}. λa. a
?132 : (A : U) -> (U) = λA. A
?133 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?134 : (S : U) -> (U) = λS. S
?135 : U = {A : U} -> ((_ : A) -> (A))
?136 : U = (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))
?137 : {A : U} -> ((_ : A) -> (A)) = λ{A}. λa. a
?138 : (A : U) -> (U) = λA. A
?139 : U = {A : U} -> ((_ : A) -> (A))
?140 : {A : U} -> ((_ : A) -> (A)) = λ{A}. λa. a
?141 : (A : U) -> (U) = λA. A
?142 : U = U
?143 : (A : U) -> ((_ : A) -> (U)) = λA. λx1. U
?144 : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> (U) = λx0. U
?145 : (h : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ({A : U} -> ((_ : A) -> (A)))) -> (U) = λh. U
?146 : (h : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ({A : U} -> ((_ : A) -> (A)))) -> ((k : {A : U} -> ((_ : A) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> (U)) = λh. λk. U
?147 : (h : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ({A : U} -> ((_ : A) -> (A)))) -> ((k : {A : U} -> ((_ : A) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((lst : (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : A) -> (A)))) -> ((_ : L) -> (L))) -> (L)))) -> (U))) = λh. λk. λlst. {A : U} -> ((_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : A) -> (A)))
?148 : (h : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ({A : U} -> ((_ : A) -> (A)))) -> ((k : {A : U} -> ((_ : A) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((lst : (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : A) -> (A)))) -> ((_ : L) -> (L))) -> (L)))) -> ({A : U} -> ((_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : A) -> (A)))))) = λh. λk. λlst. λ{A}. λx. h(x){A}
?149 : (h : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ({A : U} -> ((_ : A) -> (A)))) -> ((k : {A : U} -> ((_ : A) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((lst : (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : A) -> (A)))) -> ((_ : L) -> (L))) -> (L)))) -> ((A : U) -> ((x : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> (U))))) = λh. λk. λlst. λA. λx. A
?150 : (h : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ({A : U} -> ((_ : A) -> (A)))) -> ((k : {A : U} -> ((_ : A) -> ((_ : (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)))) -> (A)))) -> ((lst : (L : U) -> ((_ : L) -> ((_ : (_ : {A : U} -> ((_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : A) -> (A)))) -> ((_ : L) -> (L))) -> (L)))) -> (U)))
?151 : U = (x : {A : U} -> ((_ : A) -> (A))) -> ((P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P)))
?152 : (x : {A : U} -> ((_ : A) -> (A))) -> ((P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))) = λf. λP. λp. p(f{(N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))}(λN. λs. λz. z))(f{(B : U) -> ((_ : B) -> ((_ : B) -> (B)))}(λb. λt. λf. t))
?153 : U = {A : U} -> ((_ : A) -> (A))
?154 : (x : {A : U} -> ((_ : A) -> (A))) -> (U) = λx. (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))
?155 : U = {A : U} -> ((_ : A) -> (A))
?156 : {A : U} -> ((_ : A) -> (A)) = λ{A}. λx. x
?157 : U = {A : U} -> ((_ : A) -> (A))
?158 : U = (P : U) -> ((_ : (_ : (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))) -> ((_ : (B : U) -> ((_ : B) -> ((_ : B) -> (B)))) -> (P))) -> (P))
?159 : (A : U) -> (U) = λA. A
?160 : U = {S : U} -> ((_ : S) -> ((N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))))
?161 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?162 : {S : U} -> ((_ : S) -> ((N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N))))) = λ{S}. λ_. λN. λs. λz. z
?163 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?164 : (S : U) -> (U) = λS. S
?165 : U = (I : U) -> ((_ : (_ : {A : U} -> ((_ : A) -> (A))) -> (I)) -> (I))
?166 : U = {A : U} -> ((_ : A) -> (A))
?167 : U = {A : U} -> ((_ : A) -> (A))
?168 : U = (I : U) -> ((_ : (_ : {A : U} -> ((_ : A) -> (A))) -> (I)) -> (I))
?169 : (I : U) -> ((_ : (_ : {A : U} -> ((_ : A) -> (A))) -> (I)) -> (I)) = λI. λf. f(λ{A}. λa. a)
?170 : U
?171 : U = ?170
?172 : ?170
?173 : U = ?170
?174 : ?170
?175 : U = {S : U} -> ((_ : S) -> ((N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))))
?176 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?177 : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)))
?178 : (S : U) -> (U) = λS. S
?179 : U = ?78
?180 : ?78
"""

val fcpolyFullTerm = """let List : (_ : U) -> (U) = λA. (L : U) -> ((_ : L) -> ((_ : (_ : A) -> ((_ : L) -> (L))) -> (L)));
let nil : {A : ?0} -> (List(A)) = λ{A}. λL. λn. λc. n;
let cons : {A : ?1} -> ((_ : A) -> ((_ : List(A)) -> (List(A)))) = λ{A}. λa. λas. λL. λn. λc. c(a)(as(L)(n)(c));
let Bool : U = (B : U) -> ((_ : B) -> ((_ : B) -> (B)));
let true : Bool = λb. λt. λf. t;
let Pair : (_ : U) -> ((_ : U) -> (U)) = λA. λB. (P : U) -> ((_ : (_ : A) -> ((_ : B) -> (P))) -> (P));
let pair : {A : ?2} -> ({B : ?3 A} -> ((_ : A) -> ((_ : B) -> (Pair(A)(B))))) = λ{A}. λ{B}. λa. λb. λP. λp. p(a)(b);
let Nat : U = (N : U) -> ((_ : (_ : N) -> (N)) -> ((_ : N) -> (N)));
let zero : Nat = λN. λs. λz. z;
let suc : (_ : Nat) -> (Nat) = λn. λN. λs. λz. s(n(N)(s)(z));
let append : {A : ?4} -> ((_ : List(A)) -> ((_ : List(A)) -> (List(A)))) = λ{A}. λxs. λys. λL. λn. λc. xs(L)(ys(L)(n)(c))(c);
let length : {A : ?5} -> ((_ : List(A)) -> (Nat)) = λ{A}. λas. λN. λs. λz. as(N)(z)(λx. s);
let map : {A : ?6} -> ({B : ?7 A} -> ((_ : (_ : A) -> (B)) -> ((_ : List(A)) -> (List(B))))) = λ{A}. λ{B}. λf. λas. λL. λn. λc. as(L)(n)(λa. c(f(a)));
let ST : (_ : U) -> ((_ : U) -> (U)) = λS. λA. (_ : S) -> (A);
let runST : {A : ?8} -> ((_ : {S : ?9 A} -> (ST(S)(A))) -> (A)) = λ{A}. λf. f{Bool}(true);
let argST : {S : ?10} -> (ST(S)(Nat)) = λ{S}. λ_. zero;
let Id : (_ : U) -> (U) = λA. (I : U) -> ((_ : (_ : A) -> (I)) -> (I));
let mkId : {A : ?11} -> ((_ : A) -> (Id(A))) = λ{A}. λa. λI. λf. f(a);
let unId : {A : ?12} -> ((_ : Id(A)) -> (A)) = λ{A}. λi. i(?13 A i)(λx. x);
let the : (A : U) -> ((_ : A) -> (A)) = λA. λa. a;
let const : {A : ?15} -> ({B : ?16 A} -> ((_ : A) -> ((_ : B) -> (A)))) = λ{A}. λ{B}. λx. λy. x;
let IdTy : U = {A : ?17} -> ((_ : A) -> (A));
let single : {A : ?18} -> ((_ : A) -> (List(A))) = λ{A}. λa. cons{?19 A a}(a)(nil{?21 A a});
let id : {A : ?22} -> ((_ : A) -> (A)) = λ{A}. λa. a;
let ids : List(IdTy) = nil{?23};
let oneId : Id(IdTy) = mkId{?24}(λ{A}. id{?26 A});
let app : {A : ?27} -> ({B : ?28 A} -> ((_ : (_ : A) -> (B)) -> ((_ : A) -> (B)))) = λ{A}. λ{B}. id{?29 A B};
let revapp : {A : ?30} -> ({B : ?31 A} -> ((_ : A) -> ((_ : (_ : A) -> (B)) -> (B)))) = λ{A}. λ{B}. λx. λf. f(x);
let poly : (_ : IdTy) -> (Pair(Nat)(Bool)) = λf. pair{?32 f}{?33 f}(f{?36 f}(zero))(f{?38 f}(true));
let choose : {A : ?40} -> ((_ : A) -> ((_ : A) -> (A))) = λ{A}. const{?41 A}{?42 A};
let auto : (_ : IdTy) -> (IdTy) = id{?43};
let auto2 : {B : ?44} -> ((_ : IdTy) -> ((_ : B) -> (B))) = λ{B}. λ_. λb. b;
let A1 : ?45 = λx. λy. y;
let A2 : (_ : IdTy) -> (IdTy) = choose{?47}(λ{A}. id{?49 A});
let A3 : ?50 = choose{?116}(?117)(?118);
let A4 : (_ : IdTy) -> (IdTy) = λx. λ{A}. x{?52 x A}(x{?54 x A});
let A5 : ?55 = id{?125}(?126);
let A6 : {B : ?57} -> ((_ : IdTy) -> ((_ : B) -> (B))) = λ{B}. id{?58 B}(auto2{?60 B});
let A7 : ?61 = choose{?119}(?120)(?121);
let A9 : (_ : {A : ?63} -> ((_ : (_ : A) -> (A)) -> ((_ : List(A)) -> (A)))) -> (IdTy) = λf. λ{A}. f{?64 f A}(choose{?65 f A}(λ{A}. id{?68 f A A}))(ids){?69 f A};
let A10 : ?70 = poly(λ{A}. id{?127 A});
let A11 : ?72 = poly(λ{A}. λx. x);
let A12 : ?74 = id{?151}(poly)(λ{A}. λx. x);
let C1 : ?76 = length{?124}(ids);
let C2 : ?78 = id{?179}(?180);
let C3 : IdTy = λ{A}. unId{?80 A}(oneId){?81 A};
let C4 : List(IdTy) = single{?82}(λ{A}. id{?84 A});
let C5 : ?85 = cons{?139}(λ{A}. id{?141 A})(ids);
let C6 : ?87 = cons{?155}(λ{A}. λx. x)(ids);
let C7 : ?89 = append{?170}(single{?171}(?172))(single{?173}(?174));
let C8 : (_ : ?91) -> (IdTy) = λg. λ{A}. g{?93 g A}(single{?94 g A}(λ{A}. id{?96 g A A}))(ids){?97 g A};
let C9 : ?98 = map{?128}{?129}(poly)(single{?130}(λ{A}. id{?132 A}));
let C10 : ?100 = map{?165}{?166}(unId{?167})(single{?168}(oneId));
let D1 : ?102 = app{?157}{?158}(poly)(λ{A}. id{?159 A});
let D2 : ?104 = revapp{?135}{?136}(λ{A}. id{?138 A})(poly);
let D3 : ?106 = runST{?133}(λ{S}. argST{?134 S});
let D4 : ?108 = app{?175}{?176}(runST{?177})(λ{S}. argST{?178 S});
let D5 : ?110 = revapp{?160}{?161}(λ{S}. argST{?164 S})(runST{?163});
let E2 : ?112 = λh. λk. λlst. k{?147 h k lst}(λ{A}. λx. h(x){?149 h k lst A x})(lst){?150 h k lst};
let E3 : ?114 = λr. r(λ{A}. λx. λ{B}. λy. y);
U"""
