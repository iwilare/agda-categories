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
        -- begin
        --      (f.hom ⁂ g.hom) ∘ (id ⁂ A₂.d) ∘ assocˡ          ≈⟨ pullˡ ⁂∘⁂ ⟩
        --      ((f.hom ∘ id) ⁂ (g.hom ∘ A₂.d)) ∘ assocˡ        ≈⟨ ⁂-congʳ g.comm-d ⟩∘⟨refl ⟩
        --      ((f.hom ∘ id) ⁂ (B₂.d ∘ (g.hom ⁂ id))) ∘ assocˡ ≈⟨ ⁂-congˡ id-comm  ⟩∘⟨refl ⟩
        --      ((id ∘ f.hom) ⁂ (B₂.d ∘ (g.hom ⁂ id))) ∘ assocˡ ≈⟨ pushˡ (Equiv.sym ⁂∘⁂) ⟩
        --      (id ⁂ B₂.d) ∘ (f.hom ⁂ (g.hom ⁂ id)) ∘ assocˡ   ≈˘⟨ refl⟩∘⟨ assocˡ∘⁂ ⟩
        --      (id ⁂ B₂.d) ∘ assocˡ ∘ ((f.hom ⁂ g.hom) ⁂ id)   ≈⟨ sym-assoc ⟩
        --      ((id ⁂ B₂.d) ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id) ∎
        ; comm-s = {!   !} --begin
        --    A₁.s ∘ (id ⁂ A₂.s) ∘ assocˡ                            ≈⟨ pushˡ f.comm-s ⟩
        --    B₁.s ∘ (f.hom ⁂ id) ∘ (id ⁂ A₂.s) ∘ assocˡ             ≈⟨ refl⟩∘⟨ pullˡ ⁂∘⁂ ⟩
        --    B₁.s ∘ ((f.hom ∘ id) ⁂ (id ∘ A₂.s)) ∘ assocˡ           ≈⟨ refl⟩∘⟨ ⁂-congˡ id-comm ⟩∘⟨refl ⟩
        --    B₁.s ∘ ((id ∘ f.hom) ⁂ (id ∘ A₂.s)) ∘ assocˡ           ≈⟨ refl⟩∘⟨ ⁂-congʳ identityˡ ⟩∘⟨refl ⟩
        --    B₁.s ∘ ((id ∘ f.hom) ⁂ A₂.s) ∘ assocˡ                  ≈⟨ refl⟩∘⟨ ⁂-congʳ g.comm-s ⟩∘⟨refl ⟩
        --    B₁.s ∘ ((id ∘ f.hom) ⁂ (B₂.s ∘ (g.hom ⁂ id))) ∘ assocˡ ≈⟨ refl⟩∘⟨ pushˡ (Equiv.sym ⁂∘⁂) ⟩
        --    B₁.s ∘ (id ⁂ B₂.s) ∘ (f.hom ⁂ (g.hom ⁂ id)) ∘ assocˡ   ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⁂ ⟩
        --    B₁.s ∘ (id ⁂ B₂.s) ∘ assocˡ ∘ ((f.hom ⁂ g.hom) ⁂ id)   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
        --    B₁.s ∘ ((id ⁂ B₂.s) ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id) ≈⟨ sym-assoc ⟩
        --    (B₁.s ∘ (id ⁂ B₂.s) ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id) ∎
        } }
  ; identity     = {!   !} --⁂-id
  ; homomorphism = {!   !} --Equiv.sym ⁂∘⁂
  ; F-resp-≈     = {!   !} --λ (f₁≈g₁ , f₂≈g₂) → ⁂-cong₂ f₁≈g₁ f₂≈g₂
  }

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
    ; ⊚-assoc = record
      { F⇒G = record
        { η = λ { ((X PP., Y) PP., Z) →
         let module Z = MealyObj Z in
         record
          { hom = assocˡ
          ; comm-d = begin
            assocˡ ∘ ⟨ ({!   !} ∘ {!  id !}) ∘ second (Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ                                 ≈⟨ {!   !} ⟩ --refl⟩∘⟨ ⁂-congˡ ⁂-id ⟩∘⟨refl ⟩
            --assocˡ ∘ ((id ⁂ id) ⁂ Z.d) ∘ assocˡ                          ≈⟨ extendʳ assocˡ∘⁂ ⟩
            --(id ⁂ (id ⁂ Z.d)) ∘ assocˡ ∘ assocˡ                          ≈˘⟨ refl⟩∘⟨ Cartesian-Monoidal.pentagon ⟩
            --(id ⁂ (id ⁂ Z.d)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id)   ≈⟨ pullˡ ⁂∘⁂ ⟩
            --((id ∘ id) ⁂ ((id ⁂ Z.d) ∘ assocˡ)) ∘ assocˡ ∘ (assocˡ ⁂ id) ≈⟨ ⁂-congˡ identity² ⟩∘⟨refl ⟩
            --(id ⁂ ((id ⁂ Z.d) ∘ assocˡ)) ∘ assocˡ ∘ (assocˡ ⁂ id)        ≈⟨ sym-assoc ⟩
            {!   !} ∎ --((id ⁂ ((id ⁂ Z.d) ∘ assocˡ)) ∘ assocˡ) ∘ (assocˡ ⁂ id)      ∎-}
          ; comm-s = {!   !}
          } }
        ; commute = {!   !}
        ; sym-commute = {!   !}
        }
      ; F⇐G = {!   !} {-record
        { η = λ { ((X PP., Y) PP., Z) → record
          { hom = assocʳ
          ; comm-d = {!   !}
          --begin
          --   assocʳ ∘ (id ⁂ ((id ⁂ Z.d) ∘ assocˡ)) ∘ assocˡ ≈⟨ refl⟩∘⟨ {!   !} ⟩∘⟨refl ⟩
          --   assocʳ ∘ ((id ∘ id) ⁂ ((id ⁂ Z.d) ∘ assocˡ)) ∘ assocˡ ≈⟨ {!   !} ⟩
          --   assocʳ ∘ (id ⁂ (id ⁂ Z.d)) ∘ (id ⁂ assocˡ) ∘ assocˡ ≈⟨ {!   !} ⟩
          --   ((id ⁂ id) ⁂ Z.d) ∘ assocʳ ∘ (id ⁂ assocˡ) ∘ assocˡ ≈⟨ {!   !} ⟩
          --   {!   !} ≈⟨ {!   !} ⟩
          --   {!   !} ≈⟨ {!   !} ⟩
          --   {!   !} ≈⟨ {!   !} ⟩
          --   {!   !} ≈⟨ {!   !} ⟩
          --   {!   !} ∘ (assocʳ ⁂ id) ∎
          ; comm-s = {!   !}
          } }
        ; commute = {!   !}
        ; sym-commute = {!   !}
        }-}
      ; iso = {!   !}
      }
    ; unitˡ = {!   !}
    ; unitʳ = {!   !} {-record
      { F⇒G = ntHelper record
        { η = λ { (X PP., _) →
          let module X = MealyObj X in record
          { hom = π₁
          ; comm-d =
              begin π₁ ∘ ⟨ X.d ∘ second π₂ , ! ∘ π₂ ⟩ ∘ assocˡ ≈⟨ extendʳ project₁ ⟩
                    X.d ∘ second π₂ ∘ assocˡ ≈⟨ refl⟩∘⟨ thm ⟩
                    X.d ∘ (π₁ ⁂ id)          ∎
          ; comm-s =
              begin X.s ∘ (id ⁂ π₂) ∘ assocˡ ≈⟨ refl⟩∘⟨ thm ⟩
                    X.s ∘ (π₁ ⁂ id) ∎
          } }
        ; commute = λ _ → π₁∘⁂
        }
      ; F⇐G = ntHelper record
        { η = λ { (X PP., _) →
          let module X = MealyObj X in record
          { hom = ⟨ id , ! ⟩
          ; comm-d =
              begin ⟨ id , ! ⟩ ∘ X.d          ≈⟨ ⟨⟩∘ ⟩
                    ⟨ id ∘ X.d , ! ∘ X.d ⟩    ≈⟨ {!   !} ⟩
                    {!   !}                  ≈⟨ ⟨⟩-cong₂ {!   !} {!   !} ⟩
                    ⟨ (X.d ∘ second π₂) ∘ ⟨ id ∘ π₁ , (! ⁂ id) ⟩ , (! ∘ π₂) ∘ ⟨ id ∘ π₁ , (! ⁂ id) ⟩ ⟩ ≈⟨ Equiv.sym ⟨⟩∘ ⟩
                    ⟨ X.d ∘ second π₂ , ! ∘ π₂ ⟩ ∘ ⟨ id ∘ π₁ , (! ⁂ id) ⟩ ≈⟨ pushʳ (Equiv.sym assocˡ∘⟨⟩) ⟩
                    (⟨ X.d ∘ second π₂ , ! ∘ π₂ ⟩ ∘ assocˡ) ∘ ⟨ ⟨ id ∘ π₁ , ! ∘ π₁ ⟩ , id ∘ π₂ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-congʳ (Equiv.sym ⟨⟩∘) ⟩ -- ⟨⟩-congˡ {! Equiv.sym ⟨⟩∘ !} ⟩ -- refl⟩∘⟨ Equiv.sym assocˡ∘⟨⟩ ⟩
                    (⟨ X.d ∘ second π₂ , ! ∘ π₂ ⟩ ∘ assocˡ) ∘ (⟨ id , ! ⟩ ⁂ id)                   ∎
          ; comm-s =
              begin X.s ≈⟨ {!   !} ⟩
                    {!   !}   ≈⟨ {!   !} ⟩
                    {!   !}   ≈⟨ {!   !} ⟩
                    (X.s ∘ (id ⁂ π₂) ∘ assocˡ) ∘ (⟨ id , ! ⟩ ⁂ id) ∎
          } }
        ; commute = {!   !}
        }
      ; iso = λ X → record
        { isoˡ = begin
          ⟨ id , ! ⟩ ∘ π₁      ≈⟨ ⟨⟩∘ ⟩
          ⟨ id ∘ π₁ , ! ∘ π₁ ⟩ ≈⟨ unique {!   !} {!   !} ⟩
           id  ∎
        ; isoʳ = project₁
        }
      }-}
    }
  ; triangle = {!   !}
  ; pentagon = {!   !}
 }
