open import Level
open import Data.Product using (_,_)
open import Categories.Category
open import Categories.Monad
open import Categories.Category.Monoidal.Bundle
  using (SymmetricMonoidalCategory)

module Mealy {o l e} {C : SymmetricMonoidalCategory o l e} where

open import Categories.Functor
open import Categories.Category.Monoidal
open import Categories.Monad.Strong
open import Categories.Functor renaming (id to idF)
import Categories.Morphism.Reasoning as MR

open SymmetricMonoidalCategory C

-- open module SMC = SymmetricMonoidalCategory C
-- module CC = SMC.U ?

record MealyObj {I O : Obj} : Set (o ⊔ l ⊔ e) where
  field
    E : Obj
    d : E ⊗₀ I ⇒ E
    s : E ⊗₀ I ⇒ O

open MealyObj

record Mealy⇒ {I O : Obj} (X Y : MealyObj {I} {O}) : Set (o ⊔ l ⊔ e) where
  module X = MealyObj X
  module Y = MealyObj Y
  field
    hom    : X.E ⇒ Y.E
    comm-d : hom ∘ X.d ≈ Y.d ∘ Functor.F₁ (-⊗ I) hom
    comm-s : X.s ≈ Y.s ∘ Functor.F₁ (-⊗ I) hom

open Mealy⇒

Mealy : {I O : Obj} → Category (o ⊔ l ⊔ e) (o ⊔ l ⊔ e) {!   !}
Mealy {I} {O} = record
  { Obj = MealyObj {I} {O}
  ; _⇒_ = Mealy⇒
  ; _≈_ = λ f g → hom f ≈ hom g
  ; id = λ {A} → let module A = MealyObj A in
    record { hom = SymmetricMonoidalCategory.id C {A.E}
           ; comm-d = identityˡ ○ MR.introʳ U (Functor.identity ⊗)
           ; comm-s = MR.introʳ U (Functor.identity ⊗)
           }
  ; _∘_ = {!   !}
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  ; identity² = {!   !}
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  } where open HomReasoning
          -- open MR C