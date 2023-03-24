{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Category.Semigroupal.Reflection {o ℓ e} (C : Category o ℓ e) where


open import Level
open import Data.Product using (_,_; curry′)
open import Categories.Category.Core
open import Categories.Category.Semigroupal.Core 
open import Categories.Category.Semigroupal.Bundle public
open import Categories.Category.Monoidal.Core public
open import Categories.Category.Monoidal.Bundle public

open import Categories.Category.Construction.Coproduct
open import Categories.Category.Instance.One using (One)

open import Data.Maybe 
open import Data.Empty
open import Data.Unit
open import Data.Sum

open Category

thm : SemigroupalCategory o ℓ e → MonoidalCategory o ℓ e
thm S = record 
  { U = Coproduct CS (One {o} {ℓ} {e})
  ; monoidal = record
    { ⊗ = record
        { F₀ = λ {(inj₁ x , inj₁ y) → {!   !}
                ; (inj₁ x , inj₂ (lift tt)) → inj₁ x
                ; (inj₂ (lift tt) , inj₁ x) → inj₁ x
                ; (inj₂ (lift tt) , inj₂ (lift tt)) → inj₂ (lift tt)}
        ; F₁ = {!   !}
        ; identity = {!   !}
        ; homomorphism = {!   !}
        ; F-resp-≈ = {!   !}
        }
    ; unit = inj₂ (lift tt)
    ; unitorˡ = {!   !}
    ; unitorʳ = {!   !}
    ; associator = {!   !}
    ; unitorˡ-commute-from = {!   !}
    ; unitorˡ-commute-to = {!   !}
    ; unitorʳ-commute-from = {!   !}
    ; unitorʳ-commute-to = {!   !}
    ; assoc-commute-from = {!   !}
    ; assoc-commute-to = {!   !}
    ; triangle = {!   !}
    ; pentagon = {!   !}
    } 
  } where CS = SemigroupalCategory.U S