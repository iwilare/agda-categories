{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Categories.Category
open import Categories.Monad
open import Categories.Object.Terminal
open import Categories.Category.BinaryProducts
open import Categories.Category.Monoidal.Bundle
  using (SymmetricMonoidalCategory)
import Categories.Morphism.Reasoning as MR
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Cartesian.Bundle

module Mealy {o l e} (C : CartesianCategory o l e) where

open CartesianCategory C

open HomReasoning
open Terminal terminal
open BinaryProducts products
open import Categories.Morphism.Reasoning U
open import Categories.Morphism U

record MealyObj I O : Set (o ⊔ l ⊔ e) where
  field
    E : Obj
    d : E × I ⇒ E
    s : E × I ⇒ O

open MealyObj

record Mealy⇒ {I} {O} (X Y : MealyObj I O) : Set (o ⊔ l ⊔ e) where
  private
    module X = MealyObj X
    module Y = MealyObj Y
  field
    hom    : X.E ⇒ Y.E
    comm-d : hom ∘ X.d ≈ Y.d ∘ first hom
    comm-s : X.s ≈ Y.s ∘ first hom

open Mealy⇒

comp : ∀ {I} {O} {A B C : MealyObj I O} → (g : Mealy⇒ B C) → (f : Mealy⇒ A B) → Mealy⇒ A C
comp {_} {_} {A} {B} {C} g f = record
  { hom = g.hom ∘ f.hom
  ; comm-d = begin (g.hom ∘ f.hom) ∘ A.d ≈⟨ pullʳ f.comm-d ⟩
                   g.hom ∘ B.d ∘ first f.hom ≈⟨ pullˡ g.comm-d ⟩
                   (C.d ∘ first g.hom) ∘ first f.hom ≈⟨ pullʳ first∘first ⟩
                   C.d ∘ first (g.hom ∘ f.hom) ∎
  ; comm-s = begin A.s ≈⟨ f.comm-s ⟩
                   B.s ∘ first f.hom ≈⟨ g.comm-s ⟩∘⟨refl ⟩
                   (C.s ∘ first g.hom) ∘ first f.hom ≈⟨ pullʳ first∘first ⟩
                   C.s ∘ first (g.hom ∘ f.hom) ∎
  } where module f = Mealy⇒ f
          module g = Mealy⇒ g
          module A = MealyObj A
          module B = MealyObj B
          module C = MealyObj C


Mealy : ∀ I O → Category (o ⊔ l ⊔ e) (o ⊔ l ⊔ e) e
Mealy I O = record
  { Obj = MealyObj I O
  ; _⇒_ = Mealy⇒
  ; _≈_ = λ f g → hom f ≈ hom g
  ; id = λ {A} → let module A = MealyObj A in
    record { hom = id
           ; comm-d = identityˡ ○ introʳ
           first-identity
           ; comm-s = introʳ first-identity
           }
  ; _∘_ = comp
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈ = ∘-resp-≈
  }
{-
private
  variable
    I O : Obj
    X Y Z : MealyObj I O
 -}
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
        }
-}

{-
-}
