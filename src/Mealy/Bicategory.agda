{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Categories.Category
open import Categories.Bicategory
open import Categories.Functor renaming (id to idF)
open Categories.Functor.Functor
open import Categories.Functor.Construction.Constant
import Categories.Morphism.Reasoning as MR
open import Categories.Category.BinaryProducts
  using (BinaryProducts; module BinaryProducts)
open import Categories.Object.Terminal
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.Monoidal

open import Categories.Category.Cartesian.Bundle

module Mealy.Bicategory {o l e} (C : CartesianCategory o l e) where

open import Mealy C

open CartesianCategory C
open HomReasoning
open Terminal terminal
open BinaryProducts products

module Cartesian-Monoidal = Monoidal (Categories.Category.Cartesian.Monoidal.CartesianMonoidal.monoidal cartesian)

open import Categories.Morphism.Reasoning U
open import Categories.Morphism U

import Categories.Object.Product.Core as P
open import Data.Product as PP using (_,_)
import Categories.Category.Product as CP


<_^_> : ∀ {ℓ} {A : Set ℓ} → A → A → A
< f ^ g > = f

π₁′ = {!   !}
π₂′ = {!   !}

{-# DISPLAY P.Product.⟨_,_⟩ f g = < f ^ g > #-}
{-# DISPLAY P.Product.π₁ g = π₁′ #-}
{-# DISPLAY P.Product.π₂ g = π₂′ #-}



⊚ : ∀ {X Y Z} → Functor (CP.Product (Mealy Y Z) (Mealy X Y)) (Mealy X Z)
⊚ = record
  { F₀ = λ { (A , B) →
    let module A = MealyObj A
        module B = MealyObj B in
      record
        { E = A.E × B.E
        ; d = ⟨ A.d ∘ second B.s , B.d ∘ π₂ ⟩ ∘ assocˡ
        ; s = A.s ∘ second B.s ∘ assocˡ
        }}
  ; F₁ =
  λ { {A₁ PP., A₂} {B₁ PP., B₂} (f PP., g) →
    let module A₁ = MealyObj A₁
        module A₂ = MealyObj A₂
        module B₁ = MealyObj B₁
        module B₂ = MealyObj B₂
        module f = Mealy⇒ f
        module g = Mealy⇒ g in
      record
        { hom = f.hom ⁂ g.hom
        ; comm-d = begin
          (f.hom ⁂ g.hom) ∘ ⟨ A₁.d ∘ second A₂.s , A₂.d ∘ π₂ ⟩ ∘ assocˡ                                             ≈⟨ pullˡ ⁂∘⟨⟩ ⟩
          ⟨ f.hom ∘ A₁.d ∘ second A₂.s                               , g.hom ∘ A₂.d ∘ π₂ ⟩ ∘ assocˡ                  ≈⟨ ⟨⟩-congʳ  (refl⟩∘⟨ refl⟩∘⟨ ⁂-congʳ g.comm-s) ⟩∘⟨refl ⟩
          ⟨ f.hom ∘ A₁.d ∘ (id ⁂ (B₂.s ∘ first g.hom))               , g.hom ∘ A₂.d ∘ π₂ ⟩ ∘ assocˡ                  ≈⟨ ⟨⟩-congʳ  (refl⟩∘⟨ refl⟩∘⟨ Equiv.sym second∘second) ⟩∘⟨refl ⟩
          ⟨ f.hom ∘ A₁.d ∘ (id ⁂ B₂.s) ∘ (id ⁂ (g.hom ⁂ id))        , g.hom ∘ A₂.d ∘ π₂ ⟩ ∘ assocˡ                  ≈⟨ ⟨⟩-congʳ  (extendʳ f.comm-d) ⟩∘⟨refl ⟩
          ⟨ B₁.d ∘ (f.hom ⁂ id) ∘ (id ⁂ B₂.s) ∘ (id ⁂ (g.hom ⁂ id)) , g.hom ∘ A₂.d ∘ π₂ ⟩ ∘ assocˡ                ≈⟨ ⟨⟩-congʳ  (refl⟩∘⟨ pullˡ first∘second) ⟩∘⟨refl ⟩
          ⟨ B₁.d ∘ (f.hom ⁂ B₂.s) ∘ (id ⁂ (g.hom ⁂ id))             , g.hom ∘ A₂.d ∘ π₂ ⟩ ∘ assocˡ                ≈⟨ ⟨⟩-cong₂  (refl⟩∘⟨ ⁂∘⁂) sym-assoc ⟩∘⟨refl ⟩
          ⟨ B₁.d ∘ ((f.hom ∘ id) ⁂ (B₂.s ∘ (g.hom ⁂ id)))           , (g.hom ∘ A₂.d) ∘ π₂ ⟩ ∘ assocˡ                ≈⟨ ⟨⟩-cong₂  (refl⟩∘⟨ ⁂-congˡ identityʳ) (pushˡ g.comm-d) ⟩∘⟨refl ⟩
          ⟨ B₁.d ∘ (f.hom ⁂ B₂.s ∘ (g.hom ⁂ id))                    , B₂.d ∘ (g.hom ⁂ id) ∘ π₂ ⟩ ∘ assocˡ           ≈⟨ ⟨⟩-cong₂ (pushʳ (Equiv.sym second∘⁂)) (pushʳ (Equiv.sym π₂∘⁂)) ⟩∘⟨refl ⟩
          ⟨ (B₁.d ∘ second B₂.s) ∘ (f.hom ⁂ (g.hom ⁂ id))           , (B₂.d ∘ π₂) ∘ (f.hom ⁂ g.hom ⁂ id) ⟩ ∘ assocˡ ≈⟨ pushˡ (Equiv.sym ⟨⟩∘) ⟩
          ⟨ B₁.d ∘ second B₂.s , B₂.d ∘ π₂ ⟩ ∘ (f.hom ⁂ (g.hom ⁂ id)) ∘ assocˡ                                      ≈˘⟨ refl⟩∘⟨ assocˡ∘⁂ ⟩
          ⟨ B₁.d ∘ second B₂.s , B₂.d ∘ π₂ ⟩ ∘ assocˡ ∘ ((f.hom ⁂ g.hom) ⁂ id)                                      ≈⟨ sym-assoc ⟩
          (⟨ B₁.d ∘ second B₂.s , B₂.d ∘ π₂ ⟩ ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id)                                    ∎
        ; comm-s = begin
          A₁.s ∘ (id ⁂ A₂.s) ∘ assocˡ                            ≈⟨ pushˡ f.comm-s ⟩
          B₁.s ∘ (f.hom ⁂ id) ∘ (id ⁂ A₂.s) ∘ assocˡ             ≈⟨ refl⟩∘⟨ pullˡ ⁂∘⁂ ⟩
          B₁.s ∘ ((f.hom ∘ id) ⁂ (id ∘ A₂.s)) ∘ assocˡ           ≈⟨ refl⟩∘⟨ ⁂-congˡ id-comm ⟩∘⟨refl ⟩
          B₁.s ∘ ((id ∘ f.hom) ⁂ (id ∘ A₂.s)) ∘ assocˡ           ≈⟨ refl⟩∘⟨ ⁂-congʳ identityˡ ⟩∘⟨refl ⟩
          B₁.s ∘ ((id ∘ f.hom) ⁂ A₂.s) ∘ assocˡ                  ≈⟨ refl⟩∘⟨ ⁂-congʳ g.comm-s ⟩∘⟨refl ⟩
          B₁.s ∘ ((id ∘ f.hom) ⁂ (B₂.s ∘ (g.hom ⁂ id))) ∘ assocˡ ≈⟨ refl⟩∘⟨ pushˡ (Equiv.sym ⁂∘⁂) ⟩
          B₁.s ∘ (id ⁂ B₂.s) ∘ (f.hom ⁂ (g.hom ⁂ id)) ∘ assocˡ   ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⁂ ⟩
          B₁.s ∘ (id ⁂ B₂.s) ∘ assocˡ ∘ ((f.hom ⁂ g.hom) ⁂ id)   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
          B₁.s ∘ ((id ⁂ B₂.s) ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id) ≈⟨ sym-assoc ⟩
          (B₁.s ∘ (id ⁂ B₂.s) ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id) ∎
        } }
  ; identity     = ⁂-id
  ; homomorphism = Equiv.sym ⁂∘⁂
  ; F-resp-≈     = λ (f₁≈g₁ , f₂≈g₂) → ⁂-cong₂ f₁≈g₁ f₂≈g₂
  }
