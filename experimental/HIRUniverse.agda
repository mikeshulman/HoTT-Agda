{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.Equivalences
open import lib.Equivalences2
open import lib.NType
open import lib.NType2

open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Nat
open import lib.types.Unit
open import lib.types.Empty

open import lib.Funext
open import lib.Univalence

module HIRUniverse where

------------------------------
-- Some auxiliary lemmas
------------------------------

-- This can be defined in terms of existing things, but it's easier to just whack it with J.
whatever : ∀ {i} {A : Type i} {a b c : A} (p : b == a) (q : c == a) →
  p == q [ (λ x → x == a) ↓ p ∙ ! q ]
whatever idp idp = idp

-- A version of ≃ defined with nested Σs instead of a record.
_≃'_ : ∀ {i} (A B : Type i) → Type i
A ≃' B = Σ (A → B) (λ f →
         Σ (B → A) (λ g →
         Σ ((b : B) → f (g b) == b) (λ f-g →
         Σ ((a : A) → g (f a) == a) (λ g-f →
           (a : A) → ap f (g-f a) == f-g (f a)))))

-- Judgmental η makes it easy to prove that this is equivalent to the record.
≃'=≃ : ∀ {i} (A B : Type i) → (A ≃' B) == (A ≃ B)
≃'=≃ A B = ua (F , is-eq F G F-G G-F)
  where F : (A ≃' B) → (A ≃ B)
        F (f , g , f-g , g-f , adj) = (f , record {g = g ; f-g = f-g ; g-f = g-f ; adj = adj })
        G : (A ≃ B) → (A ≃' B)
        G e = (–> e , <– e , <–-inv-r e , <–-inv-l e , is-equiv.adj (snd e)) 
        F-G : (e : A ≃ B) → F (G e) == e
        F-G e = idp
        G-F : (e : A ≃' B) → G (F e) == e
        G-F e = idp

-- If [ap f] is a retraction on all points, then it's an equivalence on all points
ap-retraction-is-equiv : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  (s : (x y : A) → (f x == f y) → x == y) (r : (x y : A) (p : f x == f y) → ap f (s x y p) == p)
  → (x y : A) → is-equiv (ap f {x = x} {y = y})
ap-retraction-is-equiv {_} {A} {B} f s r x y =
  contr-map-is-equiv (λ p →
    equiv-preserves-level
      (((=Σ-eqv {B = λ a → f a == f y} (x , p) (y , idp))
        ∘e (equiv-Σ-snd (λ q → (↓-app=cst-eqv {p = q})
                               ∘e (!-equiv {x = ap f q ∙ idp} {y = p})
                               ∘e (pre∙-equiv (∙-unit-r (ap f q))))))⁻¹)
      (all-paths-is-prop (λ x1 x2 → pair=
        (s (fst x1) (fst x2) (snd x1 ∙ (! (snd x2))))
        (↓-app=cst-in (!((r (fst x1) (fst x2) (snd x1 ∙ ! (snd x2)) ∙ᵣ snd x2)
                         ∙ ∙-assoc (snd x1) (! (snd x2)) (snd x2)
                         ∙ (snd x1 ∙ₗ !-inv-l (snd x2))
                         ∙ ∙-unit-r (snd x1)))))
        (x , p) (y , idp)))

--------------------------------------------------
-- Higher inductive-recursive univalent universes
--------------------------------------------------

-- We define a general "universe operator" that takes as input an
-- arbitrary type family [E : T → Type] to include in the universe.

-- This is the module where we do HIT hacks
module Universe {i j} {T : Type i} (E : T → Type j) where

  private
    data #U : Type (lmax i j)

    #El : #U → Type j

    data #U where
      #name : (t : T) → #U
      #sig : (A : #U) → (#El A → #U) → #U
      #pi : (A : #U) → (#El A → #U) → #U
      #path : (A : #U) → #El A → #El A → #U

    #El (#name t) = E t
    #El (#sig A B) = Σ (#El A) (λ a → #El (B a))
    #El (#pi A B) = Π (#El A) (λ a → #El (B a))
    #El (#path A a b) = (a == b)

  -- HIT_README.txt recommends also a "Unit → Unit" hack to prevent
  -- misuse of absurd patterns.  I wasn't able to get that hack to
  -- work with this definition.  Maybe there is a way.  But we can
  -- just not use absurd patterns.

  U : Type (lmax i j)
  U = #U

  El : U → Type j
  El = #El

  name : (t : T) → U
  name = #name

  sig : (A : U) → (El A → U) → U
  sig = #sig

  pi : (A : U) → (El A → U) → U
  pi = #pi

  path : (A : U) → El A → El A → U
  path = #path

  postulate                     
    =ua′ : (A B : U) → (El A == El B) → A == B                      -- path-constructor
    El-=ua′ : (A B : U) (p : El A == El B) → ap El (=ua′ A B p) == p -- value of El on path constructor

  -- The eliminator, defined as a module as recommended in HIT_README
  -- (although it actually doesn't matter for us, since we never use
  -- its computation rule for the path-constructor).
  module UElim {i} {P : U → Type i}
    (name* : (t : T) → P (name t))
    (sig* : (A : U) (A* : P A) (B : El A → U) (B* : (a : El A) → P (B a)) → P (sig A B))
    (pi* : (A : U) (A* : P A) (B : El A → U) (B* : (a : El A) → P (B a)) → P (pi A B))
    (path* : (A : U) (A* : P A) (a b : El A) → P (path A a b))
    (=ua′* : (A : U) (A* : P A) (B : U) (B* : P B) (p : El A == El B)
      → A* == B* [ P ↓ =ua′ A B p ]) 
    where
    
    f : Π U P
    f = f-aux phantom where
      f-aux : Phantom =ua′* → Π U P
      f-aux phantom (#name t) = name* t
      f-aux phantom (#sig A B) =
        sig* A (f-aux phantom A) B (λ a → f-aux phantom (B a))
      f-aux phantom (#pi A B) =
        pi* A (f-aux phantom A) B (λ a → f-aux phantom (B a))
      f-aux phantom (#path A a b) =
        path* A (f-aux phantom A) a b

    postulate                   -- value of U-elim on path-constructor
      =ua′-β : (A B : U) (p : El A == El B) → apd f (=ua′ A B p) == =ua′* A (f A) B (f B) p

-- End of the HIT hacking module.

-- We start a new module so that we can keep assuming T,E in the
-- context, but are no longer peeking inside the HIT hack.
module Universe2 {i j} {T : Type i} (E : T → Type j) where

  open Universe E

  -- Let's prove that our new universes are univalent.

  ap-El-is-equiv : (A B : U) → is-equiv {A = (A == B)} (ap El)
  ap-El-is-equiv A B = ap-retraction-is-equiv El =ua′ El-=ua′ A B 

  ap-El-eqv : (A B : U) → (A == B) ≃ (El A == El B)
  ap-El-eqv A B = (ap El , ap-El-is-equiv A B)

  ua-equiv′ : (A B : U) → (El A ≃ El B) ≃ (A == B)
  ua-equiv′ A B = ap-El-eqv A B ⁻¹ ∘e ua-equiv

  -- Now let's define path spaces that compute.  We define them
  -- relative to given path-spaces for the given family [E].  At the
  -- same time as the path-spaces, we define and carry around
  -- equalities between El of them and "actual" path spaces.

  module _ (PE : (t : T) → (a1 a2 : E t) → U) (PE= : (t : T) → (a1 a2 : E t) → El (PE t a1 a2) == (a1 == a2)) where

    -- A "path-space" together with an equality to the actual one.
    path-motive : (X : Type j) → Type (lmax (lsucc j) i)
    path-motive X = (a b : X) → Σ U (λ P → El P == (a == b))

    -- For clarity, we'll define separate lemmas that handle each of
    -- the constructors of the universe.

    -- Since sig and pi have the same inputs, we put them in the same section.
    module _ (A : U) (PA : path-motive (El A)) (B : El A → U) (PB : (a : El A) → path-motive (El (B a))) where

      Psig : path-motive (El (sig A B))
      Psig (a1 , b1) (a2 , b2) = ((sig (fst (PA a1 a2)) (λ p → fst (PB a2 (transport (λ a → El (B a)) (coe (snd (PA a1 a2)) p) b1) b2))) ,
                                 Σ= (snd (PA a1 a2)) (↓-app→cst-in
                                 (λ {t} {t'} q → snd (PB a2 (transport (λ a → El (B a)) (coe (snd (PA a1 a2)) t) b1) b2)
                                                 ∙ !(ua (to-transp-equiv (λ v → El (B v)) (coe (snd (PA a1 a2)) t) {b1} {b2}))
                                                 ∙ ap (λ q' → (b1 == b2 [ (λ v → El (B v)) ↓ q' ])) (↓-idf-out (snd (PA a1 a2)) q)))
                                 ∙ =Σ-path (a1 , b1) (a2 , b2))

      Ppi : path-motive (El (pi A B))
      Ppi f1 f2 = (pi A (λ a → fst (PB a (f1 a) (f2 a))) ,
                   ap (λ P → (x : El A) → P x) (λ= (λ a → snd (PB a (f1 a) (f2 a))))
                  ∙ ua λ=-equiv)

    Pua-aux : (X : Type j) (PX : path-motive X) (Y : Type j) (PY : path-motive Y) (p : X == Y) → PX == PY [ path-motive ↓ p ]
    Pua-aux .X PX X PX' idp =
      (λ= (λ x → λ= (λ y →
        pair= (=ua′ (fst (PX x y)) (fst (PX' x y)) (snd (PX x y) ∙ !(snd (PX' x y))))
              (↓-ap-out (λ P → P == (x == y)) El _
                        (transport (λ q → (snd (PX x y) == snd (PX' x y) [ (λ P → P == (x == y)) ↓ q ]))
                                   (!(El-=ua′ (fst (PX x y)) (fst (PX' x y)) (snd (PX x y) ∙ !(snd (PX' x y)))))
                                   (whatever (snd (PX x y)) (snd (PX' x y))))))))

    Pua : (A : U) (PA : path-motive (El A)) (B : U) (PB : path-motive (El B)) (p : El A == El B) → PA == PB [ path-motive ∘ El ↓ (=ua′ A B p) ]
    Pua A PA B PB p = ↓-ap-out path-motive El (=ua′ A B p)
                               (coe! (ap (λ q → PA == PB [ path-motive ↓ q ]) (El-=ua′ A B p)) (Pua-aux (El A) PA (El B) PB p))

    module Path′ = UElim {P = λ (A : U) → path-motive (El A)}
      (λ t a b → (PE t a b , PE= t a b))
      Psig
      Ppi
      (λ A _ a1 a2 → λ p q → (path (path A a1 a2) p q , idp)) -- I think this is probably good enough
      Pua

    -- Now we break up the path-motive into its two pieces.  Here are the path-spaces.
    path′ : (A : U) (x y : El A) → U
    path′ A x y = fst (Path′.f A x y)

    -- And here are their equalities to the "real" ones.  Making this
    -- abstract prevents a stack overflow in Agda.  (During
    -- development, I made path′ abstract as well for speed and
    -- comprehensibility, but of course that breaks the desired
    -- computational behavior.)
    abstract
      path′= : (A : U) (x y : El A) → El (path′ A x y) == (x == y)
      path′= A x y = snd (Path′.f A x y)

    -- A path-space has to have an identity path.
    idp′ : (A : U) (x : El A) → El (path′ A x x)
    idp′ A x = coe! (path′= A x x) idp 

    -- Our path spaces satisfy J with a propositional computation rule.
    J′ : (A : U) (x : El A) (Z : (y : El A) → El (path′ A x y) → U) (idp* : El (Z x (idp′ A x)))
      (y : El A) (p : El (path′ A x y)) → El (Z y p)
    J′ A x Z idp* y p =
      transport (λ p' → El (Z y p')) (coe!-inv-l (path′= A x y) p)
        (J {A = El A} {a = x} (λ y q → El (Z y (coe! (path′= A x y) q))) idp* {y} (coe (path′= A x y) p))

    J′-β : (A : U) (x : El A) (Z : (y : El A) → El (path′ A x y) → U) (idp* : El (Z x (idp′ A x))) →
      J′ A x Z idp* x (idp′ A x) == idp*
    J′-β A x Z idp* =
      to-transp
        (transport (λ q → PathOver (λ p' → El (Z x p')) q (J (λ y q → El (Z y (coe! (path′= A x y) q))) idp* (coe (path′= A x x) (idp′ A x))) idp*)
                   (coe!-inv-adj (path′= A x x) idp)
                   (↓-ap-in (λ p' → El (Z x p')) (coe! (path′= A x x))
                            (apd (J {A = El A} {a = x} (λ y q → El (Z y (coe! (path′= A x y) q))) idp* {x}) (coe!-inv-r (path′= A x x) idp))))

    -- Let's verify that our path spaces compute.  In particular, they have judgmental funext.
    λ== : {A : U} {B : El A → U} (f g : El (pi A B)) → (path′ (pi A B) f g == pi A (λ x → path′ (B x) (f x) (g x)))
    λ== f g = idp

    -- Now let's internalize our equivalences and univalence.

    ap′ : (A B : U) (f : El A → El B) (x y : El A) (p : El (path′ A x y)) → El (path′ B (f x) (f y))
    ap′ A B f x y p = coe! (path′= B (f x) (f y)) (ap f (coe (path′= A x y) p)) -- could also use J′ ...

    -- The internal definition of equivalences.
    equiv′ : (A B : U) → U
    equiv′ A B = sig (pi A (λ _ → B)) (λ f →
                 sig (pi B (λ _ → A)) (λ g →
                 sig (pi B (λ b → path′ B (f (g b)) b)) (λ f-g →
                 sig (pi A (λ a → path′ A (g (f a)) a)) (λ g-f →
                     pi A (λ a → path′ (path′ B (f (g (f a))) (f a)) (ap′ A B f (g (f a)) a (g-f a)) (f-g (f a)))))))

    -- And the internalized univalence.
    equiv′= : (A B : U) → (El (equiv′ A B) == (El A ≃ El B))
    equiv′= A B =
      ua (equiv-Σ-snd (λ f →
          equiv-Σ-snd (λ g →
          equiv-Σ (equiv-Π-r (λ b → coe-equiv (path′= B (f (g b)) b))) (λ f-g →
          equiv-Σ (equiv-Π-r (λ a → coe-equiv (path′= A (g (f a)) a))) (λ g-f →
          equiv-Π-r (λ a → (pre∙-equiv (!(ap (ap f) (coe!-inv-r (path′= A (g (f a)) a) (g-f a)))))
                           ∘e (equiv-ap (coe-equiv (path′= B (f (g (f a))) (f a)) ⁻¹) _ _ ⁻¹)
                           ∘e coe-equiv (path′= (path′ B (f (g (f a))) (f a)) _ _)))))))
      ∙ ≃'=≃ (El A) (El B)

-- All of the above universes have path spaces that compute on all
-- their constructors.  This suffices for judgmental funext, but for
-- judgmental univalence we need universes that contain other
-- universes.  Thus, let's define a hierarchy of universes recursively.

-- The base types to put into the 0th universe
data T₀ : Type₀ where
  empty : T₀
  unit : T₀
  nat : T₀

E₀ : T₀ → Type₀
E₀ empty = Empty
E₀ unit = Unit
E₀ nat = ℕ

-- The hierarchy of universes and their universal families.
U : ℕ → Type₀

El : (n : ℕ) → U n → Type₀

-- The base types to put into the nth universe
T : (n : ℕ) → Type₀
T 0 = T₀
T (S n) = Coprod (U n) Unit

E : (n : ℕ) → T n → Type₀
E 0 t = E₀ t
E (S n) t = match t withl (El n) withr (λ _ → U n)

U n = Universe.U (E n)

El n = Universe.El (E n)

-- The nth universe in the (n+1)st universe
uu : (n : ℕ) → U (S n)
uu n = Universe.name (E (S n)) (inr _)

-- Lift from each universe to the next.  Note that it commutes judgmentally with El.
lift′ : (n : ℕ) → U n → U (S n)
lift′ n t = Universe.name (E (S n)) (inl t)

-- The computing path spaces for the 0th universe
PE₀ : (t : T₀) (x y : E₀ t) → U 0
PE₀ empty x y = Empty-elim x
PE₀ unit x y = Universe.name E₀ unit
PE₀ nat O O = Universe.name E₀ unit
PE₀ nat O (S y) = Universe.name E₀ empty
PE₀ nat (S x) O = Universe.name E₀ empty
PE₀ nat (S x) (S y) = PE₀ nat x y
-- We could continue this list for any other base types we want to
-- add, as long as we have a characterization of their path spaces.

PE₀= : (t : T₀) (x y : E₀ t) → (El 0 (PE₀ t x y) == (x == y))
PE₀= empty x y = Empty-elim {P = λ _ → El 0 (Empty-elim x) == (x == y)} x
PE₀= unit x y = ua ((λ _ → idp) , contr-to-contr-is-equiv (λ _ → idp) Unit-is-contr (=-preserves-level ⟨-2⟩ Unit-is-contr))
PE₀= nat O O = ua ((λ _ → idp) , contr-to-contr-is-equiv (λ _ → idp) Unit-is-contr (inhab-prop-is-contr idp (ℕ-level 0 0)))
PE₀= nat O (S y) = ua (negated-equiv-Empty (0 == S y) (ℕ-O≠S y))
PE₀= nat (S x) O = ua (negated-equiv-Empty (S x == 0) (ℕ-S≠O x))
PE₀= nat (S x) (S y) = PE₀= nat x y ∙ ua (ap S , is-eq (ap S) (ℕ-S-inj x y)
                                                       (λ _ → prop-has-all-paths (ℕ-level (S x) (S y)) _ _)
                                                       (λ _ → prop-has-all-paths (ℕ-level x y) _ _))

-- The computing path spaces for the nth universe
path′ : (n : ℕ) (A : U n) (x y : El n A) → U n

path′= : (n : ℕ) (A : U n) (x y : El n A) → El n (path′ n A x y) == (x == y)

PE : (n : ℕ) (t : T n) (x y : E n t) → U n

PE= : (n : ℕ) (t : T n) (x y : E n t) → (El n (PE n t x y) == (x == y))

PE O t x y = PE₀ t x y
PE (S n) (inl t) x y = lift′ n (path′ n t x y)
PE (S n) (inr _) A B = lift′ n (Universe2.equiv′ (E n) (PE n) (PE= n) A B)

PE= O t x y = PE₀= t x y
PE= (S n) (inl t) x y = path′= n t x y
PE= (S n) (inr _) A B = Universe2.equiv′= (E n) (PE n) (PE= n) A B ∙ ua (Universe2.ua-equiv′ (E n) A B)

path′ n = Universe2.path′ (E n) (PE n) (PE= n)

path′= n = Universe2.path′= (E n) (PE n) (PE= n)

-- Equivalences in the nth universe
equiv′ : (n : ℕ) (A B : U n) → U n
equiv′ n A B = Universe2.equiv′ (E n) (PE n) (PE= n) A B

-- Finally, let's verify that univalence is judgmental.
coe-equiv= : (n : ℕ) (A B : U n) → (path′ (S n) (uu n) A B == lift′ n (equiv′ n A B))
coe-equiv= n A B = idp
