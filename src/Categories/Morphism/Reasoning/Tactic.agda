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
module Categories.Morphism.Reasoning.Tactic {o ℓ e} (C : Category o ℓ e) where

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

open import Data.Product
open import Data.Nat using (ℕ; zero; suc)

module _ {A B} {a b : A ⇒ B} where
  skip-param : ∀ {X} (y : A ⇒ B → A ⇒ X)
    → ℕ → Set (o ⊔ ℓ ⊔ e)
  skip-param y zero = Lift (o ⊔ ℓ ⊔ e) (y a ≈ y b)
  skip-param {X = X} y (suc n) =
    ∀ {Y : Obj} {f : X ⇒ Y}
    → skip-param (λ x → f ∘ y x) n

  skip-type : ℕ → Set (o ⊔ ℓ ⊔ e)
  skip-type n = skip-param (λ x → x) n

  skip-suc : ∀ {Y} {y : A ⇒ B → A ⇒ Y} n
           → skip-param y n
           → skip-param y (suc n)
  skip-suc zero (lift h) = lift (refl⟩∘⟨ h)
  skip-suc (suc n) h = skip-suc n h

  skip : ∀ n (r : a ≈ b) → skip-type n
  skip zero r = lift r
  skip (suc n) r = skip-suc n (skip n r)

module _ where
  data MorVec : ℕ → Obj → Obj → Set (ℓ ⊔ o) where
    idV  : ∀ {A} → MorVec 1 A A
    _∘V_ : ∀ {n A B C} → B ⇒ C → MorVec n A B → MorVec (suc n) A C

  interpret : ∀ {n A B C} → MorVec n A B → C ⇒ A → C ⇒ B
  interpret idV f = f
  interpret (x ∘V v) f = x ∘ interpret v f

  skip-v : ∀ {X} n {v : MorVec n _ X} (r : a ≈ b)
         → interpret v a ≈ interpret v b
  skip-v .1 {idV} r = r
  skip-v (suc n) {x ∘V v} r = refl⟩∘⟨ skip-v n {v} r

  test-skip1 : ∀ {A B C : Obj}
             → {a b : A ⇒ B}
             → {c : B ⇒ C}
             → (r : a ≈ b)
             → c ∘ a ≈ c ∘ b
  test-skip1 r = skip-v 2 {v = _ ∘V idV} r
  test-skip2 : ∀ {A B C D : Obj}
             → {a b : A ⇒ B}
             → {c : B ⇒ C}
             → {d : C ⇒ D}
             → (r : a ≈ b)
             → d ∘ c ∘ a ≈ d ∘ c ∘ b
  test-skip2 {a = a} {b} {c} {d} r = solution2
    where
      solution1 : d ∘ c ∘ a ≈ d ∘ c ∘ b
      solution1 = skip-v 3 {v = _ ∘V (_ ∘V idV)} r
      solution2 : d ∘ c ∘ a ≈ d ∘ c ∘ b
      solution2 = Level.lower (skip 2 r)


--  gg : ∀ {A B C D E F H R : Obj}
--        {q : H ⇒ R}
--        {w : F ⇒ H}
--        {e : E ⇒ F}
--        {r : D ⇒ E}
--        {t : C ⇒ D}
--        {y : B ⇒ C}
--        {a b : A ⇒ B}
--        (p : a ≈ b)
--    → q ∘ w ∘ e ∘ r ∘ t ∘ y ∘ a
--    ≈ q ∘ w ∘ e ∘ r ∘ t ∘ y ∘ b
--  gg p = skip-v 7 {v = {!   !} ∘V ({!   !} ∘V ({!   !} ∘V {!   !}))} p -- q ∘V {! ∘V  !}} p

module _ {A B : Obj} {a : A ⇒ B} where
  take-param : ∀ {X} (k : B ⇒ X) (y : A ⇒ B → A ⇒ X)
    → ℕ → Set (o ⊔ ℓ ⊔ e)
  take-param {X} k y zero       = Lift (o ⊔ ℓ ⊔ e) (a ≈ a)
  take-param {X} k y (suc zero) = Lift (o ⊔ ℓ ⊔ e) (k ∘ a ≈ y a)
  take-param {X} k y (suc (suc n)) =
    ∀ {Y : Obj} {f : X ⇒ Y}
    → take-param (f ∘ k) (λ x → f ∘ y x) (suc n)

  take-type : ℕ → Set (o ⊔ ℓ ⊔ e)
  take-type n = ∀ {X} {f : B ⇒ X}
              → take-param f (f ∘_) n

  take-suc : ∀ {f} {y : A ⇒ B → A ⇒ Y} n
           → take-param f y (suc n)
           → take-param f y (suc (suc n))
  take-suc zero (lift a) = lift (Equiv.trans assoc (refl⟩∘⟨ a))
  take-suc (suc n) h = take-suc n h

  take : ∀ n → take-type n
  take zero = lift Equiv.refl
  take (suc zero) = lift Equiv.refl
  take (suc (suc n)) = take-suc n (take (suc n))
{-
  take-right : ∀ n → {!   !}
  take-right n = {!   !}

  take-left : ∀ n → {!   !}
  take-left n = {!   !}

  take-unwrap : ∀ n → take-type n
                    → take-left n
                    ≈ take-right n
  take-unwrap n t = {!   !}
-}

macro
  rewrite-∘ : ℕ → ℕ → ℕ → Term → Term
  rewrite-∘ s n m goal =
    skip s (Equiv.trans (Level.lower (take n))
           (Equiv.trans (r ⟩∘⟨refl)
                        (Level.lower (Equiv.sym (take n)))))
{-

solve-macro : Term → Term → TC _
solve-macro mon hole = do
  hole′ ← inferType hole >>= normalise
  names ← findCategoryNames mon
  just (lhs , rhs) ← returnTC (getArgs hole′)
    where nothing → typeError (termErr hole′ ∷ [])
  let soln = constructSoln mon names lhs rhs
  unify hole soln

macro
  solve : Term → Term → TC _
  solve = solve-macro


open import Agda.Builtin.Reflection
open import Reflection.Argument
open import Reflection.Term using (getName; _⋯⟅∷⟆_)
open import Reflection.TypeChecking.Monad.Syntax

quote Category.Equiv.trans ⟨ def ⟩ 3 ⋯⟅∷⟆ cat ⟨∷⟩
    (quote Category.Equiv.sym ⟨ def ⟩ 3 ⋯⟅∷⟆ cat ⟨∷⟩
      (quote preserves-≈ ⟨ def ⟩ 3 ⋯⟅∷⟆ cat ⟨∷⟩ buildExpr names lhs ⟨∷⟩ []) ⟨∷⟩ [])
    ⟨∷⟩
    (quote preserves-≈ ⟨ def ⟩ 3 ⋯⟅∷⟆ cat ⟨∷⟩ buildExpr names rhs ⟨∷⟩ [])
    ⟨∷⟩ []
-}


module _ {A B : Obj} {a b : A ⇒ B} (r : a ≈ b) where
  rewrite-∘ : ∀ s n m → _
  rewrite-∘ s n m = skip s (Equiv.trans {!  take n !}
                           (Equiv.trans (r ⟩∘⟨refl)
                                        {! Equiv.sym (take n)  !}))
