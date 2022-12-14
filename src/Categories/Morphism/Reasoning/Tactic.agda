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
  skip-param {X} y (suc n) =
    ∀ {Y : Obj} {f : X ⇒ Y}
    → skip-param (λ x → f ∘ y x) n

  skip-type : ℕ → Set (o ⊔ ℓ ⊔ e)
  skip-type n = skip-param (λ x → x) n

  skip-suc : ∀ {Y} {y : A ⇒ B → A ⇒ Y} n
           → skip-param y n
           → skip-param y (suc n)
  skip-suc zero (lift h) = lift (refl⟩∘⟨ h)
  skip-suc (suc n) h = skip-suc n h

  skip : ∀ n (p : a ≈ b) → skip-type n
  skip zero p = lift p
  skip (suc n) p = skip-suc n (skip n p)

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
              → take-param f (λ x → f ∘ x) n

  take-suc : ∀ {f} {y : A ⇒ B → A ⇒ Y} n
           → take-param f y (suc n)
           → take-param f y (suc (suc n))
  take-suc zero (lift a) = lift (Equiv.trans assoc (refl⟩∘⟨ a))
  take-suc (suc n) h = take-suc n h

  take : ∀ n → take-type n
  take zero = lift Equiv.refl
  take (suc zero) = lift Equiv.refl
  take (suc (suc n)) = take-suc n (take (suc n))

module _ {A B : Obj} {a : A ⇒ B} where
  rewrite-∘ : ∀ s n m → _
  rewrite-∘ s n m = {!   !}
