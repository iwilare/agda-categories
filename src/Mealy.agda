{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Categories.Category
-- open import Data.Product
open import Categories.Category.Product
open import Categories.Monad
open import Function hiding (_∘_)
open import Categories.Object.Terminal
open import Categories.Category.BinaryProducts
open import Categories.Category.Monoidal.Bundle
  using (SymmetricMonoidalCategory)

open import Categories.Category.Cartesian

module Mealy {o l e} {C : Category o l e} {K : Cartesian C} where


open module Cart = Cartesian K
open Category C

open Terminal Cart.terminal
open BinaryProducts products

open import Categories.Functor
open import Data.Product hiding (_×_)
open import Categories.Monad.Strong
open import Categories.Functor renaming (id to idF)
import Categories.Morphism.Reasoning as MR

open import Categories.Morphism C

record MealyObj I O : Set (o ⊔ l ⊔ e) where
  field
    E : Obj
    d : E × I ⇒ E
    s : E × I ⇒ O

open MealyObj

record Mealy⇒ {I} {O} (X Y : MealyObj I O) : Set (o ⊔ l ⊔ e) where
  module X = MealyObj X
  module Y = MealyObj Y
  field
    hom    : X.E ⇒ Y.E
    comm-d : hom ∘ X.d ≈ Y.d ∘ first hom
    comm-s : X.s ≈ Y.s ∘ first hom

open Mealy⇒

comp : ∀ {I} {O} {A B C : MealyObj I O} → (f : Mealy⇒ A B) → (g : Mealy⇒ B C) → Mealy⇒ A C
comp f g = record
  { hom = g.hom ∘ f.hom
  ; comm-d = begin _ ≈⟨ MR.pullʳ C f.comm-d ⟩
                   _ ≈⟨ MR.pullˡ C g.comm-d ⟩
                   _ ≈⟨ MR.pullʳ C (Equiv.sym {!   !}) ⟩
                   _ ∎
  ; comm-s = begin _ ≈⟨ f.comm-s ⟩
                   _ ≈⟨ (g.comm-s ⟩∘⟨refl) ⟩
                   _ ≈⟨ MR.pullʳ C (Equiv.sym {!   !}) ⟩
                   _ ∎
  } where module f = Mealy⇒ f
          module g = Mealy⇒ g
          open HomReasoning

Mealy : ∀ I O → Category (o ⊔ l ⊔ e) (o ⊔ l ⊔ e) e
Mealy I O = record
  { Obj = MealyObj I O
  ; _⇒_ = Mealy⇒
  ; _≈_ = λ f g → hom f ≈ hom g
  ; id = λ {A} → let module A = MealyObj A in
    record { hom = {! SymmetricMonoidalCategory.id C {A.E}  !} -- SymmetricMonoidalCategory.id C {A.E}
           ; comm-d = identityˡ ○ MR.introʳ C {!   !}
           ; comm-s = MR.introʳ C {!   !}
           }
  ; _∘_ = flip comp
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈ = ∘-resp-≈
  } where open HomReasoning

private
  variable
    I O : Obj
    X Y Z : MealyObj I O

{-
2Mealy : Category o (o ⊔ l ⊔ e) (l ⊔ e)
2Mealy = record
  { Obj = Obj
  ; _⇒_ = λ X Y → MealyObj {X} {Y}
  ; _≈_ = _≈ₑ_
  ; id = record { E = ⊤ ; d = ! ; s = π₂ }
  ; _∘_ = _∘ₑ_ --_∘ₑ_
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  ; identity² = {!   !}
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  } where
      record _≈ₑ_ {X} {Y} (A B : MealyObj {X} {Y}) : Set (l ⊔ e) where
            module A = MealyObj A
            module B = MealyObj B
            field
              e-iso : A.E ≅ B.E
            module e-iso = _≅_ e-iso
            field
              d-iso : e-iso.from ∘ A.d ≈ B.d ∘ Functor.F₁ (-× X) e-iso.from
              s-iso : A.s ≈ B.s ∘ Functor.F₁ (-× X) e-iso.from
      _∘ₑ_ : ∀ {X Y Z : Obj} (B : MealyObj {Y} {Z}) → (A : MealyObj {X} {Y}) → MealyObj {X} {Z}
      B ∘ₑ A = let module A = MealyObj A in let module B = MealyObj B in record
        { E = B.E × A.E
        ; d = second A.d ∘ assocˡ
        ; s = B.s ∘ second A.s ∘ assocˡ
        }
      assocₑ : {X Y Z W : Obj} {A : MealyObj {X} {Y}} {B : MealyObj {Y} {Z}} {C : MealyObj {Z} {W}} → ((C ∘ₑ B) ∘ₑ A) ≈ₑ (C ∘ₑ (B ∘ₑ A))
      assocₑ {A = A} {B = B} {C = C} = let module A = MealyObj A in let module B = MealyObj B in let module C = MealyObj C in record
        { e-iso = ≅.sym ×-assoc
        ; d-iso = {!   !}
        ; s-iso = {!   !}
        } where open HomReasoning
-}

mealy-comp : {X Y Z : Obj} →
      Functor
      (Product (Mealy Y Z) (Mealy X Y))
      (Mealy X Z)
mealy-comp = record
  { F₀ = λ {(M1 , M2) → record
    { E = E M1 × E M2
    ; d = {!   !}
    ; s = MealyObj.s M1 ∘ second (MealyObj.s M2) ∘ BinaryProducts.assocˡ products
    }}
  ; F₁ = {!   !}
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  }