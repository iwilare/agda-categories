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
open import Categories.NaturalTransformation using ()
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

{-
<_,,_> : ∀ {ℓ} {A : Set ℓ} → A → A → A
< f ,, g > = f

Aπ₁ = {!   !}
Aπ₂ = {!   !}

{-# DISPLAY P.Product.⟨_,_⟩ f g = < f ,, g > #-}
{-# DISPLAY P.Product.π₁ g = Aπ₁ #-}
{-# DISPLAY P.Product.π₂ g = Aπ₂ #-}
-}

MealyBicategory : Bicategory (o ⊔ l ⊔ e) (o ⊔ l ⊔ e) e o
MealyBicategory = record
  { enriched = record
    { Obj = Obj
    ; hom = Mealy
    ; id = const (record
      { E = ⊤
      ; d = !
      ; s = π₂
      })
    ; ⊚ = ⊚
    ; ⊚-assoc = λ {A B C D} → record
      { F⇒G = record
        { η = λ { ((X PP., Y) PP., Z) → record
          { hom = assocˡ
          ; comm-d = {!   !} {- begin
            assocˡ ∘ (id ⁂ MealyObj.d Z) ∘ assocˡ                                 ≈˘⟨ refl⟩∘⟨ ⁂-congˡ ⁂-id ⟩∘⟨refl ⟩
            assocˡ ∘ ((id ⁂ id) ⁂ MealyObj.d Z) ∘ assocˡ                          ≈⟨ extendʳ assocˡ∘⁂ ⟩
            (id ⁂ (id ⁂ MealyObj.d Z)) ∘ assocˡ ∘ assocˡ                          ≈˘⟨ refl⟩∘⟨ Cartesian-Monoidal.pentagon ⟩
            (id ⁂ (id ⁂ MealyObj.d Z)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id)   ≈⟨ pullˡ ⁂∘⁂ ⟩
            ((id ∘ id) ⁂ ((id ⁂ MealyObj.d Z) ∘ assocˡ)) ∘ assocˡ ∘ (assocˡ ⁂ id) ≈⟨ ⁂-congˡ identity² ⟩∘⟨refl ⟩
            (id ⁂ ((id ⁂ MealyObj.d Z) ∘ assocˡ)) ∘ assocˡ ∘ (assocˡ ⁂ id)        ≈⟨ sym-assoc ⟩
            ((id ⁂ ((id ⁂ MealyObj.d Z) ∘ assocˡ)) ∘ assocˡ) ∘ (assocˡ ⁂ id)      ∎-}
          ; comm-s = {!   !}
          } }
        ; commute = {!   !}
        ; sym-commute = {!   !}
        }
      ; F⇐G = record
        { η = λ { ((X PP., Y) PP., Z) → record
          { hom = assocʳ
          ; comm-d = begin
             assocʳ ∘ (id ⁂ ((id ⁂ MealyObj.d Z) ∘ assocˡ)) ∘ assocˡ ≈⟨ refl⟩∘⟨ {!   !} ⟩∘⟨refl ⟩
             assocʳ ∘ ((id ∘ id) ⁂ ((id ⁂ MealyObj.d Z) ∘ assocˡ)) ∘ assocˡ ≈⟨ {!   !} ⟩
             assocʳ ∘ (id ⁂ (id ⁂ MealyObj.d Z)) ∘ (id ⁂ assocˡ) ∘ assocˡ ≈⟨ {!   !} ⟩
             ((id ⁂ id) ⁂ MealyObj.d Z) ∘ assocʳ ∘ (id ⁂ assocˡ) ∘ assocˡ ≈⟨ {!   !} ⟩
             {!   !} ≈⟨ {!   !} ⟩
             {!   !} ≈⟨ {!   !} ⟩
             {!   !} ≈⟨ {!   !} ⟩
             {!   !} ≈⟨ {!   !} ⟩
             {!   !} ∘ (assocʳ ⁂ id) ∎
          ; comm-s = {!   !}
          } }
        ; commute = {!   !}
        ; sym-commute = {!   !}
        }
      ; iso = {!   !}
      -- λ X → record
      --  { isoˡ = assocʳ∘assocˡ
      --  ; isoʳ = assocˡ∘assocʳ
      --  }
      }
    ; unitˡ = {!   !}
    ; unitʳ = {!   !}
    }
  ; triangle = {!   !}
  ; pentagon = {!   !}
  } where
    ⊚ : ∀ {X Y Z} → Functor (CP.Product (Mealy Y Z) (Mealy X Y)) (Mealy X Z)
    ⊚ = record
      { F₀ = λ { (A , B) →
        let module A = MealyObj A
            module B = MealyObj B in
         record
           { E = A.E × B.E
           ; d = second B.d ∘ assocˡ
           ; s = A.s ∘ second B.s ∘ assocˡ
           }}
      ; F₁ = λ { {A₁ PP., A₂} {B₁ PP., B₂} (f PP., g) →
        let module A₁ = MealyObj A₁
            module A₂ = MealyObj A₂
            module B₁ = MealyObj B₁
            module B₂ = MealyObj B₂
            module f = Mealy⇒ f
            module g = Mealy⇒ g in
          record
            { hom = f.hom ⁂ g.hom
            ; comm-d = {!   !}
{-               begin
                 (f.hom ⁂ g.hom) ∘ (id ⁂ A₂.d) ∘ assocˡ          ≈⟨ pullˡ ⁂∘⁂ ⟩
                 ((f.hom ∘ id) ⁂ (g.hom ∘ A₂.d)) ∘ assocˡ        ≈⟨ ⁂-congʳ g.comm-d ⟩∘⟨refl ⟩
                 ((f.hom ∘ id) ⁂ (B₂.d ∘ (g.hom ⁂ id))) ∘ assocˡ ≈⟨ ⁂-congˡ id-comm  ⟩∘⟨refl ⟩
                 ((id ∘ f.hom) ⁂ (B₂.d ∘ (g.hom ⁂ id))) ∘ assocˡ ≈⟨ pushˡ (Equiv.sym ⁂∘⁂) ⟩
                 (id ⁂ B₂.d) ∘ (f.hom ⁂ (g.hom ⁂ id)) ∘ assocˡ   ≈˘⟨ refl⟩∘⟨ assocˡ∘⁂ ⟩
                 (id ⁂ B₂.d) ∘ assocˡ ∘ ((f.hom ⁂ g.hom) ⁂ id)   ≈⟨ sym-assoc ⟩
                 ((id ⁂ B₂.d) ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id) ∎-}
            ; comm-s = {!   !}
{-              begin
                A₁.s ∘ (id ⁂ A₂.s) ∘ assocˡ                            ≈⟨ pushˡ f.comm-s ⟩
                B₁.s ∘ (f.hom ⁂ id) ∘ (id ⁂ A₂.s) ∘ assocˡ             ≈⟨ refl⟩∘⟨ pullˡ ⁂∘⁂ ⟩
                B₁.s ∘ ((f.hom ∘ id) ⁂ (id ∘ A₂.s)) ∘ assocˡ           ≈⟨ refl⟩∘⟨ ⁂-congˡ id-comm ⟩∘⟨refl ⟩
                B₁.s ∘ ((id ∘ f.hom) ⁂ (id ∘ A₂.s)) ∘ assocˡ           ≈⟨ refl⟩∘⟨ ⁂-congʳ identityˡ ⟩∘⟨refl ⟩
                B₁.s ∘ ((id ∘ f.hom) ⁂ A₂.s) ∘ assocˡ                  ≈⟨ refl⟩∘⟨ ⁂-congʳ g.comm-s ⟩∘⟨refl ⟩
                B₁.s ∘ ((id ∘ f.hom) ⁂ (B₂.s ∘ (g.hom ⁂ id))) ∘ assocˡ ≈⟨ refl⟩∘⟨ pushˡ (Equiv.sym ⁂∘⁂) ⟩
                B₁.s ∘ (id ⁂ B₂.s) ∘ (f.hom ⁂ (g.hom ⁂ id)) ∘ assocˡ   ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⁂ ⟩
                B₁.s ∘ (id ⁂ B₂.s) ∘ assocˡ ∘ ((f.hom ⁂ g.hom) ⁂ id)   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
                B₁.s ∘ ((id ⁂ B₂.s) ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id) ≈⟨ sym-assoc ⟩
                (B₁.s ∘ (id ⁂ B₂.s) ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id) ∎-}
            } }
      ; identity = {!   !} --⁂-id
      ; homomorphism = {!   !} --Equiv.sym ⁂∘⁂
      ; F-resp-≈ = {!   !} --λ (f₁≈g₁ , f₂≈g₂) → ⁂-cong₂ f₁≈g₁ f₂≈g₂
      }
