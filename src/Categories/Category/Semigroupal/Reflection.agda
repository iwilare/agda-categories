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

open Category

thm : SemigroupalCategory o ℓ e → MonoidalCategory o ℓ e
thm S = record 
  { U = record
    { Obj = Maybe (Obj CS)
    ; _⇒_ = λ {(just X) (just Y) → CS [ X , Y ]
             ; (just X) nothing → {!   !}
             ; nothing (just Y) → {!   !}
             ; nothing nothing → {!   !}}
    ; _≈_ = {!   !} 
    ; id = {!   !}
    ; _∘_ = {!   !}
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