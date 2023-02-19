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

{-
associazione : {X Y Z A B : Obj} {C = C₁ : Obj} {D : Obj} →
      NaturalIsomorphism (⊚ {X = X} {Y = Y} {Z = Z} ∘F (⊚ {X = Y} {Y = {! X  !}} {Z = Z} ∘F CP.πˡ CP.※ idF ∘F CP.πʳ))
      (⊚ ∘F
       (idF ∘F CP.πˡ CP.※ ⊚ ∘F CP.πʳ) ∘F
       (CP.πˡ ∘F CP.πˡ CP.※ CP.πʳ ∘F CP.πˡ CP.※ CP.πʳ))
associazione = record
  { F⇒G = record
    { η = λ { ((X PP., Y) PP., Z) →
      let module Z = MealyObj Z in record
        { hom = assocˡ
        ; comm-d = {!   !}
        ; comm-s = {!   !}
        } }
    ; commute = {!   !}
    ; sym-commute = {!   !}
    }
  ; F⇐G = {!   !}
  ; iso = {!   !}
  }
-}

{-
<_^_> : ∀ {ℓ} {A : Set ℓ} → A → A → A
< f ^ g > = f

π₁′ = {!   !}
π₂′ = {!   !}

{-# DISPLAY P.Product.⟨_,_⟩ f g = < f ^ g > #-}
{-# DISPLAY P.Product.π₁ g = π₁′ #-}
{-# DISPLAY P.Product.π₂ g = π₂′ #-}
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
    ; unitʳ = unitr
    }
  ; triangle = {!   !}
  ; pentagon = {!   !}
 } where
    unitr : ∀ {A B} → _
    unitr = record
      { F⇒G = ntHelper record
        { η = λ (_ PP., X) →
          let module X = MealyObj X in record
          { hom = π₂
          ; comm-d = begin
            π₂ ∘ ⟨ ! ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ , X.d ∘ π₂ ⟩ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ≈⟨ extendʳ project₂ ⟩
            X.d ∘ π₂ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ≈⟨ refl⟩∘⟨ project₂ ⟩
            X.d ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ (Equiv.sym identityˡ) ⟩
            X.d ∘ ⟨ π₂ ∘ π₁ , id ∘ π₂ ⟩ ∎
          ; comm-s = begin
            π₂ ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ≈⟨ extendʳ project₂ ⟩
            X.s ∘ π₂ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ≈⟨ refl⟩∘⟨ project₂ ⟩
            X.s ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ (Equiv.sym identityˡ) ⟩
            X.s ∘ ⟨ π₂ ∘ π₁ , id ∘ π₂ ⟩ ∎
          }
        ; commute = λ _ → project₂
        }
      ; F⇐G = ntHelper record
        { η = λ (_ PP., X) →
          let module X = MealyObj X in record
          { hom = ⟨ ! , id ⟩
          ; comm-d = begin
            ⟨ ! , id ⟩ ∘ X.d ≈⟨ ⟨⟩∘ ⟩
            ⟨ ! ∘ X.d , id ∘ X.d ⟩ ≈⟨ ⟨⟩-congˡ id-comm-sym ⟩
            ⟨ ! ∘ X.d , X.d ∘ id ⟩  ≈⟨ ⟨⟩-cong₂ (Equiv.sym (!-unique _)) (refl⟩∘⟨ Equiv.sym ⁂-id) ⟩
            ⟨ ! , X.d ∘ ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ (!-unique _) (Equiv.sym (pullʳ project₂)) ⟩
            ⟨ (! ∘ (id ⁂ X.s)) ∘ ⟨ ! ∘ π₁ , ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩ , (X.d ∘ π₂) ∘ ⟨ ! ∘ π₁ , ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩ ⟩ ≈⟨ Equiv.sym ⟨⟩∘ ⟩
            ⟨ ! ∘ (id ⁂ X.s) , X.d ∘ π₂ ⟩ ∘ ⟨ ! ∘ π₁ , ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩              ≈⟨ Equiv.sym (pullʳ assocˡ∘⟨⟩) ⟩
            (⟨ ! ∘ (id ⁂ X.s) , X.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (⟨ ⟨ ! ∘ π₁ , id ∘ π₁ ⟩ , id ∘ π₂ ⟩) ≈˘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
            (⟨ ! ∘ (id ⁂ X.s) , X.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (⟨ ! , id ⟩ ⁂ id)                    ∎
          ; comm-s = begin
            X.s ≈⟨ introʳ ⁂-id ⟩
            X.s ∘ ⟨ id ∘ π₁ , id ∘ π₂ ⟩                                               ≈˘⟨ refl⟩∘⟨ project₂ ⟩
            X.s ∘ π₂ ∘ ⟨ ! ∘ π₁ , ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩                             ≈˘⟨ extendʳ project₂ ⟩
            π₂ ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ ∘ ⟨ ! ∘ π₁ , ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⟨⟩ ⟩
            π₂ ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ ∘ assocˡ ∘ ⟨ ⟨ ! ∘ π₁ , id ∘ π₁ ⟩ , id ∘ π₂ ⟩ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
            π₂ ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ ∘ assocˡ ∘ (⟨ ! , id ⟩ ⁂ id)                  ≈˘⟨ Equiv.trans assoc (refl⟩∘⟨ assoc) ⟩
            (π₂ ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ ∘ assocˡ) ∘ (⟨ ! , id ⟩ ⁂ id)                ∎
          }
        ; commute = λ (_ PP., f) →
          let module f = Mealy⇒ f in begin
            ⟨ ! , id ⟩ ∘ f.hom         ≈⟨ ⟨⟩∘ ⟩
            ⟨ ! ∘ f.hom , id ∘ f.hom ⟩ ≈⟨ ⟨⟩-cong₂ (Equiv.trans (Equiv.sym (!-unique _)) (Equiv.sym identityˡ)) id-comm-sym ⟩
            ⟨ id ∘ ! , f.hom ∘ id ⟩    ≈⟨ ⁂∘⟨⟩ ⟩
            (id ⁂ f.hom) ∘ ⟨ ! , id ⟩
        }
      ; iso = λ X → record { isoˡ = begin
            ⟨ ! , id ⟩ ∘ π₂ ≈⟨ ⟨⟩∘ ⟩
            ⟨ ! ∘ π₂ , id ∘ π₂ ⟩ ≈⟨ unique !-unique₂ id-comm ⟩
            id ∎ ; isoʳ = project₂ }
      }
