{-# OPTIONS --without-K --safe #-}
open import Categories.Category

{-
  Helper routines most often used in reasoning with commutative squares,
  at the level of arrows in categories.

  Basic  : reasoning about identity
  Pulls  : use a ∘ b ≈ c as left-to-right rewrite
  Pushes : use c ≈ a ∘ b as a left-to-right rewrite
  IntroElim : introduce/eliminate an equivalent-to-id arrow
  Extend : 'extends' a commutative square with an equality on left/right/both
-}
module Categories.Morphism.Reasoning.Core {o ℓ e} (C : Category o ℓ e) where

open import Level using (Level; _⊔_; Lift; lift)
open import Function renaming (id to idᶠ; _∘_ to _∙_)

open import Relation.Binary hiding (_⇒_)

open Category C
open Definitions C

private
  variable
    X Y : Obj
    a a′ a″ b b′ b″ c c′ c″ : X ⇒ Y
    f g h i : X ⇒ Y

open HomReasoning

module Basic where
  id-unique : ∀ {o} {f : o ⇒ o} → (∀ g → g ∘ f ≈ g) → f ≈ id
  id-unique g∘f≈g = Equiv.trans (Equiv.sym identityˡ) (g∘f≈g id)

  id-comm : ∀ {a b} {f : a ⇒ b} → f ∘ id ≈ id ∘ f
  id-comm = Equiv.trans identityʳ (Equiv.sym identityˡ)

  id-comm-sym : ∀ {a b} {f : a ⇒ b} → id ∘ f ≈ f ∘ id
  id-comm-sym = Equiv.trans identityˡ (Equiv.sym identityʳ)

open Basic public

module Utils where
  assoc² : ((i ∘ h) ∘ g) ∘ f ≈ i ∘ (h ∘ (g ∘ f))
  assoc² = Equiv.trans assoc assoc

  assoc²' : (i ∘ (h ∘ g)) ∘ f ≈ i ∘ (h ∘ (g ∘ f))
  assoc²' = Equiv.trans assoc (∘-resp-≈ʳ assoc)

  assoc²'' : i ∘ ((h ∘ g) ∘ f) ≈ (i ∘ h) ∘ (g ∘ f)
  assoc²'' = Equiv.trans (∘-resp-≈ʳ assoc) sym-assoc

open Utils public

module Pulls (ab≡c : a ∘ b ≈ c) where

  pullʳ : (f ∘ a) ∘ b ≈ f ∘ c
  pullʳ {f = f} = begin
    (f ∘ a) ∘ b ≈⟨ assoc ⟩
    f ∘ (a ∘ b) ≈⟨ refl⟩∘⟨ ab≡c ⟩
    f ∘ c       ∎

  pullˡ : a ∘ b ∘ f ≈ c ∘ f
  pullˡ {f = f} = begin
    a ∘ b ∘ f   ≈⟨ sym-assoc ⟩
    (a ∘ b) ∘ f ≈⟨ ab≡c ⟩∘⟨refl ⟩
    c ∘ f       ∎

open Pulls public

module Pushes (c≡ab : c ≈ a ∘ b) where
  pushʳ : f ∘ c ≈ (f ∘ a) ∘ b
  pushʳ {f = f} = begin
    f ∘ c       ≈⟨ refl⟩∘⟨ c≡ab ⟩
    f ∘ (a ∘ b) ≈⟨ sym-assoc ⟩
    (f ∘ a) ∘ b ∎

  pushˡ : c ∘ f ≈ a ∘ (b ∘ f)
  pushˡ {f = f} = begin
    c ∘ f       ≈⟨ c≡ab ⟩∘⟨refl ⟩
    (a ∘ b) ∘ f ≈⟨ assoc ⟩
    a ∘ (b ∘ f) ∎

open Pushes public

module IntroElim (a≡id : a ≈ id) where
  elimʳ : f ∘ a ≈ f
  elimʳ {f = f} = begin
    f ∘ a  ≈⟨ refl⟩∘⟨ a≡id ⟩
    f ∘ id ≈⟨ identityʳ ⟩
    f      ∎

  introʳ : f ≈ f ∘ a
  introʳ = Equiv.sym elimʳ

  elimˡ : (a ∘ f) ≈ f
  elimˡ {f = f} = begin
    a ∘ f  ≈⟨ a≡id ⟩∘⟨refl ⟩
    id ∘ f ≈⟨ identityˡ ⟩
    f      ∎

  introˡ : f ≈ a ∘ f
  introˡ = Equiv.sym elimˡ

  intro-center : f ∘ g ≈ f ∘ a ∘ g
  intro-center = ∘-resp-≈ʳ introˡ

  elim-center : f ∘ a ∘ g ≈ f ∘ g
  elim-center = ∘-resp-≈ʳ elimˡ

open IntroElim public

module Extends (s : CommutativeSquare f g h i) where
  extendˡ : CommutativeSquare f g (a ∘ h) (a ∘ i)
  extendˡ {a = a} = begin
    (a ∘ h) ∘ f ≈⟨ pullʳ s ⟩
    a ∘ i ∘ g   ≈⟨ sym-assoc ⟩
    (a ∘ i) ∘ g ∎

  extendʳ : CommutativeSquare (f ∘ a) (g ∘ a) h i
  extendʳ {a = a} = begin
    h ∘ (f ∘ a) ≈⟨ pullˡ s ⟩
    (i ∘ g) ∘ a ≈⟨ assoc ⟩
    i ∘ (g ∘ a) ∎

  extend² : CommutativeSquare (f ∘ b) (g ∘ b) (a ∘ h) (a ∘ i)
  extend² {b = b} {a = a } = begin
    (a ∘ h) ∘ (f ∘ b) ≈⟨ pullʳ extendʳ ⟩
    a ∘ (i ∘ (g ∘ b)) ≈⟨ sym-assoc ⟩
    (a ∘ i) ∘ (g ∘ b) ∎

open Extends public

-- essentially composition in the arrow category
{-
   A₁ -- c --> B₁
   |           |
   b′  comm    b
   |           |
   V           V
   A₂ -- c′ -> B₂
   |           |
   a′  comm    a
   |           |
   V           V
   A₃ -- c″ -> B₃

   then the whole diagram commutes
-}
glue : CommutativeSquare c′ a′ a c″ →
       CommutativeSquare c b′ b c′ →
       CommutativeSquare c (a′ ∘ b′) (a ∘ b) c″
glue {c′ = c′} {a′ = a′} {a = a} {c″ = c″} {c = c} {b′ = b′} {b = b} sq-a sq-b = begin
  (a ∘ b) ∘ c    ≈⟨ pullʳ sq-b ⟩
  a ∘ (c′ ∘ b′)  ≈⟨ pullˡ sq-a ⟩
  (c″ ∘ a′) ∘ b′ ≈⟨ assoc ⟩
  c″ ∘ (a′ ∘ b′) ∎

glue◃◽ : a ∘ c′ ≈ c″ → CommutativeSquare c b′ b c′ → CommutativeSquare c b′ (a ∘ b) c″
glue◃◽ {a = a} {c′ = c′} {c″ = c″} {c = c} {b′ = b′} {b = b} tri-a sq-b = begin
  (a ∘ b) ∘ c   ≈⟨ pullʳ sq-b ⟩
  a ∘ (c′ ∘ b′) ≈⟨ pullˡ tri-a ⟩
  c″ ∘ b′       ∎

glue◃◽′ : c ∘ c′ ≈ a′ → CommutativeSquare a b a′ b′ → CommutativeSquare (c′ ∘ a) b c b′
glue◃◽′ {c = c} {c′ = c′} {a′ = a′} {a = a} {b = b} {b′ = b′} tri sq = begin
  c ∘ c′ ∘ a ≈⟨ pullˡ tri ⟩
  a′ ∘ a     ≈⟨ sq ⟩
  b′ ∘ b     ∎

glue◽◃ : CommutativeSquare a b a′ b′ → b ∘ c ≈ c′ → CommutativeSquare (a ∘ c) c′ a′ b′
glue◽◃ {a = a} {b = b} {a′ = a′} {b′ = b′} {c = c} {c′ = c′} sq tri = begin
  a′ ∘ a ∘ c   ≈⟨ pullˡ sq ⟩
  (b′ ∘ b) ∘ c ≈⟨ pullʳ tri ⟩
  b′ ∘ c′      ∎

glue▹◽ : b ∘ a″ ≈ c → CommutativeSquare a b a′ b′ → CommutativeSquare (a ∘ a″) c a′ b′
glue▹◽ {b = b} {a″ = a″} {c = c} {a = a} {a′ = a′} {b′ = b′} tri sq = begin
  a′ ∘ a ∘ a″   ≈⟨ pullˡ sq ⟩
  (b′ ∘ b) ∘ a″ ≈⟨ pullʳ tri ⟩
  b′ ∘ c        ∎

-- essentially composition in the over category
glueTrianglesʳ : a ∘ b ≈ a′ → a′ ∘ b′ ≈ a″ → a ∘ (b ∘ b′) ≈ a″
glueTrianglesʳ {a = a} {b = b} {a′ = a′} {b′ = b′} {a″ = a″} a∘b≡a′ a′∘b′≡a″ = begin
  a ∘ (b ∘ b′) ≈⟨ pullˡ a∘b≡a′ ⟩
  a′ ∘ b′      ≈⟨ a′∘b′≡a″ ⟩
  a″           ∎

-- essentially composition in the under category
glueTrianglesˡ : a′ ∘ b′ ≈ b″ → a ∘ b ≈ b′ → (a′ ∘ a) ∘ b ≈ b″
glueTrianglesˡ {a′ = a′} {b′ = b′} {b″ = b″} {a = a} {b = b} a′∘b′≡b″ a∘b≡b′ = begin
  (a′ ∘ a) ∘ b ≈⟨ pullʳ a∘b≡b′ ⟩
  a′ ∘ b′      ≈⟨ a′∘b′≡b″ ⟩
  b″           ∎

module Cancellers (inv : h ∘ i ≈ id) where

  cancelʳ : (f ∘ h) ∘ i ≈ f
  cancelʳ {f = f} = begin
    (f ∘ h) ∘ i ≈⟨ pullʳ inv ⟩
    f ∘ id      ≈⟨ identityʳ ⟩
    f           ∎

  insertʳ : f ≈ (f ∘ h) ∘ i
  insertʳ = Equiv.sym cancelʳ

  cancelˡ : h ∘ (i ∘ f) ≈ f
  cancelˡ {f = f} = begin
    h ∘ (i ∘ f) ≈⟨ pullˡ inv ⟩
    id ∘ f      ≈⟨ identityˡ ⟩
    f           ∎

  insertˡ : f ≈ h ∘ (i ∘ f)
  insertˡ = Equiv.sym cancelˡ

  cancelInner : (f ∘ h) ∘ (i ∘ g) ≈ f ∘ g
  cancelInner {f = f} {g = g} = begin
    (f ∘ h) ∘ (i ∘ g) ≈⟨ pullˡ cancelʳ ⟩
    f ∘ g             ∎

open Cancellers public

center : g ∘ h ≈ a → (f ∘ g) ∘ h ∘ i ≈ f ∘ a ∘ i
center {g = g} {h = h} {a = a} {f = f} {i = i} eq = begin
  (f ∘ g) ∘ h ∘ i ≈⟨ assoc ⟩
  f ∘ g ∘ h ∘ i   ≈⟨ refl⟩∘⟨ pullˡ eq ⟩
  f ∘ a ∘ i       ∎

center⁻¹ : f ∘ g ≈ a → h ∘ i ≈ b →  f ∘ (g ∘ h) ∘ i ≈ a ∘ b
center⁻¹ {f = f} {g = g} {a = a} {h = h} {i = i} {b = b} eq eq′ = begin
  f ∘ (g ∘ h) ∘ i ≈⟨ refl⟩∘⟨ pullʳ eq′ ⟩
  f ∘ g ∘ b       ≈⟨ pullˡ eq ⟩
  a ∘ b           ∎

pull-last : h ∘ i ≈ a → (f ∘ g ∘ h) ∘ i ≈ f ∘ g ∘ a
pull-last {h = h} {i = i} {a = a} {f = f} {g = g} eq = begin
  (f ∘ g ∘ h) ∘ i ≈⟨ assoc ⟩
  f ∘ (g ∘ h) ∘ i ≈⟨ refl⟩∘⟨ pullʳ eq ⟩
  f ∘ g ∘ a       ∎

pull-first : f ∘ g ≈ a → f ∘ (g ∘ h) ∘ i ≈ a ∘ h ∘ i
pull-first {f = f} {g = g} {a = a} {h = h} {i = i} eq = begin
  f ∘ (g ∘ h) ∘ i ≈⟨ refl⟩∘⟨ assoc ⟩
  f ∘ g ∘ h ∘ i   ≈⟨ pullˡ eq ⟩
  a ∘ h ∘ i       ∎

pull-center : g ∘ h ≈ a → f ∘ g ∘ h ∘ i ≈ f ∘ a ∘ i
pull-center eq = ∘-resp-≈ʳ (pullˡ eq)

push-center : g ∘ h ≈ a → f ∘ a ∘ i ≈ f ∘ g ∘ h ∘ i
push-center eq = Equiv.sym (pull-center eq)

intro-first : a ∘ b ≈ id → f ∘ g ≈ a ∘ (b ∘ f) ∘ g
intro-first {a = a} {b = b} {f = f} {g = g} eq = begin
  f ∘ g           ≈⟨ introˡ eq ⟩
  (a ∘ b) ∘ f ∘ g ≈⟨ assoc ⟩
  a ∘ b ∘ f ∘ g   ≈˘⟨ refl⟩∘⟨ assoc ⟩
  a ∘ (b ∘ f) ∘ g ∎

intro-last : a ∘ b ≈ id → f ∘ g ≈ f ∘ (g ∘ a) ∘ b
intro-last {a = a} {b = b} {f = f} {g = g} eq = begin
  f ∘ g           ≈⟨ introʳ eq ⟩
  (f ∘ g) ∘ a ∘ b ≈⟨ assoc ⟩
  f ∘ g ∘ a ∘ b   ≈˘⟨ refl⟩∘⟨ assoc ⟩
  f ∘ (g ∘ a) ∘ b ∎

open import Data.Product

module _ {A B} {a b : A ⇒ B} (p : a ≈ b) where
  open import Data.Nat using (ℕ; zero; suc)

  skip-param : ∀ {Y} (y : A ⇒ B → A ⇒ Y)
       → ℕ → Set (o ⊔ ℓ ⊔ e)
  skip-param y zero = Lift (o ⊔ ℓ ⊔ e) (y a ≈ y b)
  skip-param {Y = Y} y (suc n) =
    ∀ {G : Obj} {k : Y ⇒ G}
        → skip-param (λ x → k ∘ y x) n

  skip-type : ℕ → Set (o ⊔ ℓ ⊔ e)
  skip-type n = skip-param (λ x → x) n

  skip-suc : ∀ {Y} {y : A ⇒ B → A ⇒ Y} n
             → skip-param y n
             → skip-param y (suc n)
  skip-suc zero (lift h) = lift (refl⟩∘⟨ h)
  skip-suc (suc n) h = skip-suc n h

  skip : ∀ n → skip-type n
  skip zero = lift p
  skip (suc n) = skip-suc n (skip n)

module _ {A B : Obj} {a : A ⇒ B} where
  open import Data.Nat using (ℕ; zero; suc)

  assoc-general : ∀ {X}
           (f : B ⇒ X)
           (y : A ⇒ B → A ⇒ X)
         → ℕ → Set (o ⊔ ℓ ⊔ e)
  assoc-general {X} f y zero =
    Lift (o ⊔ ℓ ⊔ e) (f ∘ a ≈ y a)
  assoc-general {X} f y (suc n) =
    ∀ {Y : Obj} {f' : X ⇒ Y}
        → assoc-general (f' ∘ f) (λ x → f' ∘ y x) n

  assoc-id : ℕ → Set (o ⊔ ℓ ⊔ e)
  assoc-id n = ∀ {X} {f : B ⇒ X}
             → assoc-general f (λ x → f ∘ x) n

  assoc-suc : ∀ {f} {y : A ⇒ B → A ⇒ Y} n
            → assoc-general f y n
            → assoc-general f y (suc n)
  assoc-suc zero (lift a) = lift (Equiv.trans assoc (refl⟩∘⟨ a))
  assoc-suc (suc n) h = assoc-suc n h

  assoc-proof : ∀ n → assoc-id n
  assoc-proof zero = lift Equiv.refl
  assoc-proof (suc n) = assoc-suc n (assoc-proof n)

  _ : {! assoc-suc  !}
  _ = {!   !}

{-


a (b c d f)
(a b c d) f

a (b c d e f)
(a b c d e) f



(a b c d) f = a b c d f
------------ instanziando f
(a b c d) (f g) = a b c d f g
(a (b c d)) (f g)
a (b c d) (f g) = a b c d f g



((a b c d) f) p = (a b c d f) p




    (l a ∘ b ≈ a ∘ r b)
    ((a ∘ l k) ∘ b ≈ a ∘ (k ∘ r b))
    ((a ∘ k ∘ l k') ∘ b ≈ a ∘ k ∘ (k' ∘ r b))
-}
{-
  assocs : ∀ {A B C D X Y} {a : A ⇒ B} {b : C ⇒ D}
           (l : {!   !} ⇒ {!   !} → {!   !} ⇒ {!   !})
           (r : {!   !} ⇒ {!   !} → {!   !} ⇒ {!   !})
         → ℕ → Set (o ⊔ ℓ ⊔ e)
  assocs {A} {B} {C} {D} {a} {b} l r zero =
  assocs {A} {B} {C} {D} {a} {b} l r (suc n) =
    ∀ {k : {!   !} ⇒ {!   !}} →
    Lift (o ⊔ ℓ ⊔ e) ((a ∘ l k) ∘ b ≈ a ∘ (k ∘ r b))
    Lift (o ⊔ ℓ ⊔ e) ((a ∘ k ∘ l k') ∘ b ≈ a ∘ k ∘ (k' ∘ r b))
  assocs {A} {B} {C} {D} {a} {b} l r (suc (suc n)) =
    ∀ {k  : {!   !} ⇒ {!   !}} →
      {k' : {!   !} ⇒ {!   !}} →
    Lift (o ⊔ ℓ ⊔ e) ((a ∘ k ∘ l k') ∘ b ≈ a ∘ k ∘ (k' ∘ r b))
  assocs {A} {B} {C} {D} {a} {b} l r (suc (suc (suc n))) =
    ∀ {P G : Obj} {k : {!   !} ⇒ {!   !}}
        → assocs {!   !} --(λ x → l x ∘ k)
                 {!   !} --(λ x → r x) --k ∘ ?)
                 n

  assoc-general : ∀ {A B C D X Y} {a : A C.⇒ B} {b : C C.⇒ D}
           (l : {!   !} C.⇒ {!   !} → {!   !} C.⇒ {!   !})
           (r : {!   !} C.⇒ {!   !} → {!   !} C.⇒ {!   !})
         → ℕ → Set (o ⊔ ℓ ⊔ e)
  assoc-general {A} {B} {C} {D} {a} {b} l r zero =
    Lift (o ⊔ ℓ ⊔ e) (l a ∘ b C.≈ a ∘ r b)
  assoc-general {A} {B} {C} {D} {a} {b} l r (suc n) =
    ∀ {P G : C.Obj} {k : {! P  !} C.⇒ {! G !}}
        → kriatur-definitive
                (λ x → x ∘ l k)
                (λ x → k ∘ r x)
                n






  --l a ∘ r b C.≈ l a ∘ r b

  n1ormalata : ℕ → Set (o ⊔ ℓ ⊔ e)
  n1ormalata n = assocs {!   !} {!   !} n --(λ x → x) (λ x → {!   !}) n --(λ x → x) (λ x → x) n
{-

  l1emmatorum : ∀ {G} {n} {k : {!   !}}
             → assocs (λ x → x) n
             → assocs (λ x → k C.∘ x) n
  l1emmatorum {n = zero} = {!   !}
  l1emmatorum {n = suc n} = {! lemma {n = n}  !}

  t1rasc : ∀ n → skip-type n
  t1rasc zero = lift ? --p
  t1rasc (suc n) = l1emmatorum (t1rasc n)

  t1est-miracolo = {! skip-type 4  !} --{! skip-type 4  !}
-}


  -- ∀ {C D : Obj} → param-skip-param-1 {!   !}

  {-


  {-
  skip-param : (a ≈ b)
          ∀ {hs : DepVecArrows (f) n}
          → repeat hs n a
          → repeat hs n b
  skip-param = ?

  -}


  {-
  skip-param-1 : {A B C : Obj} {C = C₁ : Obj} {D : Obj} {f : A ⇒ B} {g : B ⇒ C₁} {r : _} {l : _} {h : C₁ ⇒ D}
            → h ∘ a
            → h ∘ b

  skip-param-2 : {A B C : Obj} {C = C₁ : Obj} {D : Obj} {f : A ⇒ B} {g : B ⇒ C₁} {r : _} {l : _} {h : C₁ ⇒ D}
            → h ∘ h' ∘ a
            → h ∘ h' ∘ b

  skip-param-3 : {A B C : Obj} {C = C₁ : Obj} {D : Obj} {f : A ⇒ B} {g : B ⇒ C₁} {r : _} {l : _} {h : C₁ ⇒ D}
            → h ∘ h' ∘ h'' ∘ a
            → h ∘ h' ∘ h'' ∘ b
            -}

  _ : {A B : Obj} {C = C₁ : Obj} {D : Obj} {f : A ⇒ B} {g : B ⇒ C₁}
    → g ∘ f ≈ g ∘ f
  _ = {!   !}

  _ : {A B : Obj} {C = C₁ : Obj} {D : Obj} {f : A ⇒ B} {g : B ⇒ C₁} {h : C₁ ⇒ D} → (h ∘ g) ∘ f ≈ h ∘ g ∘ f
  _ = {!   !}
  {-
  veritàbase : {A B C : Obj} {C = C₁ : Obj} {D : Obj} {f : A ⇒ B} {g : B ⇒ C₁} {r : veritàbase} {h : C₁ ⇒ D}
    → (h ∘ g ∘ r) ∘ f ≈ h ∘ g ∘ r ∘ f
  veritàbase = {!   !}

  expandveritàbase : {A B C : Obj} {C = C₁ : Obj} {D : Obj} {f : A ⇒ B} {g : B ⇒ C₁} {r : e} {h : C₁ ⇒ D}
      (h ∘ g ∘ r) ∘ f ≈ h ∘ g ∘ r ∘ f
    → (h ∘ g ∘ r ∘ l) ∘ f ≈ h ∘ g ∘ r ∘ l ∘ f
  expandveritàbase = {!   !}


  _ : {A B C : Obj} {C = C₁ : Obj} {D : Obj} {f : A ⇒ B} {g : B ⇒ C₁} {r : _} {l : _} {h : C₁ ⇒ D}
    → (h ∘ g ∘ r ∘ l) ∘ f ≈ h ∘ g ∘ r ∘ l ∘ f
  _ = {!   !}
  -}
  -}
-}



{-
      (h ∘ g ∘ r) ∘ f ≈ h ∘ g ∘ r ∘ f
      (h ∘ g ∘ r) ∘ l ∘ f ≈ h ∘ g ∘ r ∘ l ∘ f
      (h ∘ (g ∘ r ∘ l)) ∘ f
      -}
