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


⟨_^_⟩ : {X = X₁ : Obj} {A = A₁ : Obj} {B = B₁ : Obj} →
      X₁ ⇒ A₁ → X₁ ⇒ B₁ → X₁ ⇒ {!   !} --P.Product.A×B product
⟨ f ^ g ⟩ = f --⟨ f , g ⟩

π₁′ = π₁
π₂′ = π₂


{-# DISPLAY P.Product.⟨_,_⟩ f g = ⟨ f ^ g ⟩ #-}
{-# DISPLAY P.Product.π₁ g = π₁′ #-}
{-# DISPLAY P.Product.π₂ g = π₂′ #-}
--{-# DISPLAY P.Product.⟨_,_⟩ (π₁′ ∘ π₁′) (⟨ π₂′ ∘ π₁′ ^ π₂′ ⟩) = assocˡ #-}

{-
asdf : ∀ {A B C} → π₂ ∘ assocˡ {A = A} {B = B} {C = C} ≈ (assocʳ ⁂ id)
asdf = begin
    π₂ ∘ assocˡ
  ≈⟨ project₂ ⟩
    ⟨ π₂ ∘ π₁ ^ π₂ ⟩
  ≈˘⟨ {!   !} ⟩
    {!   !}
  ≈˘⟨ {!   !} ⟩
    {!   !}
  ≈˘⟨ {!   !} ⟩
    {!   !}
  ≈˘⟨ {!   !} ⟩
    {!  assocʳ ⁂ id !}
  ∎
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
      { F⇒G = ntHelper record
        { η = λ { ((X PP., Y) PP., Z) →
         let module X = MealyObj X in
         let module Y = MealyObj Y in
         let module Z = MealyObj Z in
         record
          { hom = assocˡ
          ; comm-d = begin
            assocˡ ∘ ⟨ (⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ≈⟨ {!   !} ⟩
            {!   !} ≈⟨ {!   !} ⟩
            {!   !} ≈⟨ {!   !} ⟩
            (⟨ X.d ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) , (⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ) ∘ π₂ ⟩ ∘ assocˡ) ∘ (assocˡ ⁂ id) ∎
          ; comm-s = begin
            (X.s ∘ (id ⁂ Y.s) ∘ assocˡ) ∘ (id ⁂ Z.s) ∘ assocˡ                             ≈⟨ Equiv.trans assoc (refl⟩∘⟨ assoc) ⟩
            X.s ∘ (id ⁂ Y.s) ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ                               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assocˡ∘second ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ assocˡ ∘ assocˡ                        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ Cartesian-Monoidal.pentagon ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ second∘second ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ ((id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ ∘ (assocˡ ⁂ id)      ≈⟨ refl⟩∘⟨ pullˡ second∘second ⟩
            X.s ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ ∘ (assocˡ ⁂ id)             ≈˘⟨ Equiv.trans assoc (refl⟩∘⟨ assoc) ⟩
            (X.s ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ) ∘ (assocˡ ⁂ id)           ∎
          } }
        ; commute = λ ((X PP., Y) PP., Z) → assocˡ∘⁂
        }
      ; F⇐G = ntHelper record
        { η = λ { ((X PP., Y) PP., Z) →
         let module X = MealyObj X in
         let module Y = MealyObj Y in
         let module Z = MealyObj Z in
         record
          { hom = assocʳ
          ; comm-d = begin
            assocʳ ∘ ⟨ X.d ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) , (⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ) ∘ π₂ ⟩ ∘ assocˡ ≈⟨ {! assocˡ ∘ (assocʳ ⁂ id)  !} ⟩
            assocʳ ∘ ⟨ (X.d ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ))) ∘ assocˡ , ((⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ) ∘ π₂) ∘ assocˡ ⟩  ≈⟨ {! assocˡ  !} ⟩
            assocʳ ∘ ⟨ X.d ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ , ⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ∘ π₂ ∘ assocˡ ⟩  ≈⟨ ⟨⟩∘ ⟩
            ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ ⟨ _ , _ ⟩ , (π₂ ∘ π₂) ∘ ⟨ _ , _ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ (⟨⟩-congʳ (Equiv.sym identityˡ) ⟩∘⟨refl) (pullʳ project₂) ⟩
            ⟨ (id ⁂ π₁) ∘ ⟨ _ , _ ⟩ , π₂ ∘ _ ⟩                       ≈⟨ ⟨⟩-cong₂ second∘⟨⟩ (pullˡ project₂) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s ∘ (id ⁂ Z.s) ∘ assocˡ) ∘ assocˡ , π₁ ∘ ⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ∘ π₂ ∘ assocˡ ⟩ , (Z.d ∘ π₂) ∘ assocˡ ∘ π₂ ∘ assocˡ ⟩ ≈⟨ ⟨⟩-cong₂ (⟨⟩-congˡ (pullˡ project₁)) {!   !} ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s ∘ (id ⁂ Z.s) ∘ assocˡ) ∘ assocˡ , (Y.d ∘ (id ⁂ Z.s)) ∘ assocˡ ∘ π₂ ∘ assocˡ ⟩ , Z.d ∘ π₂ ∘ assocˡ ∘ π₂ ∘ assocˡ ⟩ ≈⟨ ⟨⟩-cong₂ {!   !} (refl⟩∘⟨ {! refl⟩∘⟨ ?  !}) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s ∘ (id ⁂ Z.s) ∘ assocˡ) ∘ assocˡ , (Y.d ∘ (id ⁂ Z.s)) ∘ assocˡ ∘ π₂ ∘ assocˡ ⟩ , Z.d ∘ π₂ ∘ assocˡ ∘ (assocʳ ⁂ id) ⟩ ≈⟨ {!   !} ⟩






            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ , Z.d ∘ π₂ ∘ assocˡ ∘ (assocʳ ⁂ id) ⟩ ≈⟨ {! assocˡ  !} ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ ((assocˡ ∘ assocʳ) ⁂ id) , Z.d ∘ π₂ ∘ assocˡ ∘ (assocʳ ⁂ id) ⟩ ≈⟨ {!   !} ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ∘ (assocʳ ⁂ id) , Z.d ∘ π₂ ∘ assocˡ ∘ (assocʳ ⁂ id) ⟩
              ≈˘⟨ ⟨⟩-cong₂ (Equiv.trans assoc (Equiv.trans (refl⟩∘⟨ assoc) (Equiv.trans (refl⟩∘⟨ refl⟩∘⟨ assoc) (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc)))) (Equiv.trans assoc (refl⟩∘⟨ assoc)) ⟩
            {!   !} ≈⟨ {!   !} ⟩ --⟨ (⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id)) ∘ (assocʳ ⁂ id) , (Z.d ∘ π₂ ∘ assocˡ) ∘ (assocʳ ⁂ id) ⟩ ≈˘⟨ ⟨⟩∘ ⟩
            {!   !} ≈⟨ {!   !} ⟩ --⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) , Z.d ∘ π₂ ∘ assocˡ ⟩ ∘ (assocʳ ⁂ id) ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ refl⟩∘⟨ Cartesian-Monoidal.pentagon) ⟩∘⟨refl ⟩
            {!   !} ≈⟨ {!   !} ⟩ --⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ assocˡ ∘ assocˡ , Z.d ∘ π₂ ∘ assocˡ ⟩ ∘ (assocʳ ⁂ id)                        ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ extendʳ (Equiv.sym assocˡ∘second)) ⟩∘⟨refl ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ ∘ (assocʳ ⁂ id)
            , Z.d ∘ π₂ ∘ assocˡ ∘ (assocʳ ⁂ id) ⟩
              ≈˘⟨ ⟨⟩-cong₂ (Equiv.trans assoc (refl⟩∘⟨ assoc)) assoc ⟩
            ⟨ (⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ ∘ (id ⁂ Z.s)) ∘ assocˡ ∘ (assocʳ ⁂ id)
            , (Z.d ∘ π₂) ∘ assocˡ ∘ (assocʳ ⁂ id) ⟩
              ≈⟨ Equiv.sym ⟨⟩∘ ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ∘ (assocʳ ⁂ id)                                      ≈˘⟨ ⟨⟩-congʳ assoc ⟩∘⟨refl ⟩
            ⟨ (⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ∘ (assocʳ ⁂ id)                                    ≈˘⟨ assoc ⟩
            (⟨ (⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (assocʳ ⁂ id)                                  ∎
          ; comm-s = begin
            X.s ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ                                               ≈⟨ refl⟩∘⟨ pushˡ (Equiv.sym second∘second) ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ ((id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ                                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (Equiv.sym second∘second) ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ                                   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ introʳ ⁂-id ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (id ⁂ id)                       ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⁂-congˡ assocˡ∘assocʳ ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ ((assocˡ ∘ assocʳ) ⁂ id)        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ first∘first ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ∘ (assocʳ ⁂ id)   ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ Equiv.trans assoc (refl⟩∘⟨ assoc) ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ ((id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id)) ∘ (assocʳ ⁂ id) ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (Equiv.sym Cartesian-Monoidal.pentagon) ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ assocˡ ∘ assocˡ ∘ (assocʳ ⁂ id)                          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assocˡ∘second ⟩
            X.s ∘ (id ⁂ Y.s) ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ ∘ (assocʳ ⁂ id) ≈˘⟨ Equiv.trans assoc (Equiv.trans (refl⟩∘⟨ assoc) (Equiv.trans assoc (refl⟩∘⟨ assoc))) ⟩
            ((X.s ∘ (id ⁂ Y.s) ∘ assocˡ) ∘ (id ⁂ Z.s) ∘ assocˡ) ∘ (assocʳ ⁂ id) ∎
          } }
        ; commute = λ ((X PP., Y) PP., Z) → assocʳ∘⁂
        }
      ; iso = λ X → record { isoˡ = assocʳ∘assocˡ ; isoʳ = assocˡ∘assocʳ }
      }
    ; unitˡ = record
      { F⇒G = ntHelper record
        { η = λ (_ PP., X) →
          let module X = MealyObj X in
          let lemma : π₂ ∘ assocˡ ≈ π₂ ⁂ id
              lemma = begin
                π₂ ∘ assocˡ           ≈⟨ project₂ ⟩
                ⟨ π₂ ∘ π₁ , π₂ ⟩      ≈⟨ ⟨⟩-congˡ (Equiv.sym identityˡ) ⟩
                ⟨ π₂ ∘ π₁ , id ∘ π₂ ⟩ ∎ in
          record
          { hom = π₂
          ; comm-d = begin
            π₂ ∘ ⟨ ! ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ , X.d ∘ π₂ ⟩ ∘ assocˡ ≈⟨ extendʳ project₂ ⟩
            X.d ∘ π₂ ∘ assocˡ                                       ≈⟨ refl⟩∘⟨ lemma ⟩
            X.d ∘ ⟨ π₂ ∘ π₁ , id ∘ π₂ ⟩                             ∎
          ; comm-s = begin
            π₂ ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ ∘ assocˡ ≈⟨ extendʳ project₂ ⟩
            X.s ∘ π₂ ∘ assocˡ                    ≈⟨ refl⟩∘⟨ lemma ⟩
            X.s ∘ ⟨ π₂ ∘ π₁ , id ∘ π₂ ⟩          ∎
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
            ⟨ id ∘ ! , f.hom ∘ id ⟩    ≈˘⟨ ⁂∘⟨⟩ ⟩
            (id ⁂ f.hom) ∘ ⟨ ! , id ⟩  ∎
        }
      ; iso = λ X → record { isoˡ = begin
            ⟨ ! , id ⟩ ∘ π₂ ≈⟨ ⟨⟩∘ ⟩
            ⟨ ! ∘ π₂ , id ∘ π₂ ⟩ ≈⟨ unique !-unique₂ id-comm ⟩
            id ∎ ; isoʳ = project₂ }
      }
    ; unitʳ = record
      { F⇒G = ntHelper record
        { η = λ (X PP., _) →
          let module X = MealyObj X in
          let lemma : (id ⁂ π₂) ∘ assocˡ ≈ (π₁ ⁂ id)
              lemma = begin
                ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ           ≈⟨ ⁂∘⟨⟩ ⟩
                ⟨ id ∘ π₁ ∘ π₁ , π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ identityˡ (Equiv.trans project₂ (Equiv.sym identityˡ)) ⟩
                ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩ ∎ in
              record
          { hom = π₁
          ; comm-d = begin
            π₁ ∘ ⟨ X.d ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ , ! ∘ π₂ ⟩ ∘ assocˡ ≈⟨ extendʳ project₁ ⟩
            X.d ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ ≈⟨ refl⟩∘⟨ lemma ⟩
            X.d ∘ ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩ ∎
          ; comm-s = begin
            X.s ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ ≈⟨ refl⟩∘⟨ lemma ⟩
            X.s ∘ ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩  ∎
          }
        ; commute = λ _ → project₁
        }
      ; F⇐G = ntHelper record
        { η = λ (X PP., _) →
          let module X = MealyObj X in record
          { hom = ⟨ id , ! ⟩
          ; comm-d = begin
            ⟨ id , ! ⟩ ∘ X.d ≈⟨ ⟨⟩∘ ⟩
            ⟨ id ∘ X.d , ! ∘ X.d ⟩ ≈⟨ ⟨⟩-congʳ id-comm-sym ⟩
            ⟨ X.d ∘ id , ! ∘ X.d ⟩ ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ Equiv.sym ⁂-id) ⟩
            ⟨ X.d ∘ ⟨ id ∘ π₁ , id ∘ π₂ ⟩ , ! ∘ X.d ⟩ ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ ⟨⟩-cong₂ (refl⟩∘⟨ Equiv.sym identityˡ) (Equiv.sym project₂)) ⟩
            ⟨ X.d ∘ ⟨ id ∘ id ∘ π₁ , π₂ ∘ ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩  , ! ∘ X.d ⟩ ≈⟨ ⟨⟩-cong₂ (Equiv.sym (pullʳ ⁂∘⟨⟩)) !-unique₂ ⟩
            ⟨ (X.d ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩) ∘ ⟨ id ∘ π₁ , ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩ , (! ∘ π₂) ∘ ⟨ id ∘ π₁ , ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩ ⟩ ≈⟨ Equiv.sym ⟨⟩∘ ⟩
            ⟨ X.d ∘ (id ⁂ π₂) , ! ∘ π₂ ⟩ ∘ ⟨ id ∘ π₁ , ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩ ≈⟨ Equiv.sym (pullʳ assocˡ∘⟨⟩) ⟩
            (⟨ X.d ∘ (id ⁂ π₂) , ! ∘ π₂ ⟩ ∘ assocˡ) ∘ ⟨ ⟨ id ∘ π₁ , ! ∘ π₁ ⟩ , id ∘ π₂ ⟩ ≈˘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
            (⟨ X.d ∘ (id ⁂ π₂) , ! ∘ π₂ ⟩ ∘ assocˡ) ∘ (⟨ id , ! ⟩ ⁂ id) ∎
          ; comm-s = begin
            X.s ≈⟨ introʳ ⁂-id ⟩
            X.s ∘ ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ≈˘⟨ refl⟩∘⟨ ⟨⟩-cong₂ (pullˡ identity²) project₂ ⟩
            X.s ∘ ⟨ id ∘ id ∘ π₁ , π₂ ∘ ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩ ≈˘⟨ refl⟩∘⟨ ⁂∘⟨⟩ ⟩
            X.s ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ ⟨ id ∘ π₁ , ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⟨⟩ ⟩
            X.s ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ ∘ ⟨ ⟨ id ∘ π₁ , ! ∘ π₁ ⟩ , id ∘ π₂ ⟩ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
            X.s ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ ∘ ⟨ ⟨ id , ! ⟩ ∘ π₁ , id ∘ π₂ ⟩ ≈˘⟨ Equiv.trans assoc (refl⟩∘⟨ assoc) ⟩
            (X.s ∘  ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ) ∘ ⟨ ⟨ id , ! ⟩ ∘ π₁ , id ∘ π₂ ⟩ ∎
          }
        ; commute = λ (f PP., _) →
          let module f = Mealy⇒ f in begin
            ⟨ id , ! ⟩ ∘ f.hom         ≈⟨ ⟨⟩∘ ⟩
            ⟨ id ∘ f.hom , ! ∘ f.hom ⟩ ≈⟨ ⟨⟩-cong₂ id-comm-sym (Equiv.trans (Equiv.sym (!-unique _)) (Equiv.sym identityˡ)) ⟩
            ⟨ f.hom ∘ id  , id ∘ ! ⟩   ≈˘⟨ ⁂∘⟨⟩ ⟩
            (f.hom ⁂ id) ∘ ⟨ id , ! ⟩  ∎
        }
      ; iso = λ X → record
        { isoˡ =
         begin
           ⟨ id , ! ⟩ ∘ π₁ ≈⟨ ⟨⟩∘ ⟩
           ⟨ id ∘ π₁ , ! ∘ π₁ ⟩ ≈⟨ unique id-comm !-unique₂ ⟩
           id ∎
        ; isoʳ = project₁
        }
      }
    }
 ; triangle = Cartesian-Monoidal.triangle
 ; pentagon = Cartesian-Monoidal.pentagon
 }
