{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Category.Semigroupal.Reflection {o ℓ e} (C : Category o ℓ e) where


open import Level

open import Categories.Category.Core
open import Categories.Category.Semigroupal.Core 
open import Categories.Category.Semigroupal.Bundle public
open import Categories.Category.Monoidal.Core public
open import Categories.Category.Monoidal.Bundle public
open import Data.Maybe 
open import Data.Empty
open import Data.Unit

open Category

thm : SemigroupalCategory o ℓ e → MonoidalCategory o ℓ e
thm S = record 
  { U = record
    { Obj = Maybe (Obj CS)
    ; _⇒_ = λ {(just X) (just Y) → CS [ X , Y ]
               ; (just X) nothing → Lift ℓ ⊥
               ; nothing (just Y) → Lift ℓ ⊥
               ; nothing nothing → Lift ℓ ⊤
               }
    ; _≈_ = λ { {just X} {just Y} f g → (CS ≈ f) g
              ; {nothing} {nothing} f g → Lift e ⊤ 
              }
    ; id = λ { {just X} → Category.id CS {X}
             ; {nothing} → lift tt
             }
    ; _∘_ = λ { {just A} {just B} {just C} f g → (CS ∘ f) g
              ; {nothing} {nothing} {nothing} f g → lift tt
              }
    ; assoc = {!   !}
    ; sym-assoc = {!   !}
    ; identityˡ = {!   !}
    ; identityʳ = {!   !}
    ; identity² = {!   !}
    ; equiv = {!   !}
    ; ∘-resp-≈ = {!   !}
    } 
  ; monoidal = {!   !} 
  } where CS = SemigroupalCategory.U S
          -- open Category CS