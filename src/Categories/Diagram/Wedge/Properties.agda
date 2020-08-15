{-# OPTIONS --without-K --safe #-}

-- This is more a pair of constructions that a property...
-- but show that one can build a Cone for the Twisted Arrow functor from a Wedge
-- and vice-versa.

open import Categories.Category
open import Categories.Functor.Bifunctor

module Categories.Diagram.Wedge.Properties {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where

private
  module C = Category C
  module D = Category D
  open D
  open HomReasoning
  variable
    A : Obj

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Category.Construction.TwistedArrow
open import Categories.Diagram.Cone
open import Categories.Diagram.Wedge F
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor.Properties
open import Categories.Functor.Construction.Constant
open import Categories.Functor.Instance.Twisted C D
import Categories.Morphism as M
open import Categories.Morphism.Reasoning D
open import Categories.NaturalTransformation.Dinatural

open Functor F

-- There is a construction that builds a Cone (Twist F) from a Wedge
module _ (w : Wedge)  where
  open Wedge w
  open DinaturalTransformation
  open Morphism
  open Morphism⇒

  private
    Wedge-to-Cone′ : {C C′ : C.Obj} (f : C C.⇒ C′) → Wedge.E w ⇒ F₀ (C , C′)
    Wedge-to-Cone′ {C} {C′} f = F₁ (C.id , f) ∘ α dinatural C

  Wedge-to-Cone : Cone (Twist F)
  Wedge-to-Cone = record
    { N = E
    ; apex = record
      { ψ = λ Tw → Wedge-to-Cone′ (arr Tw)
      ; commute = λ { {record { dom = dom₁ ; cod = cod₁ ; arr = arr₁ }}
                      {record { dom = dom ; cod = cod ;  arr = arr }}
                      (record { dom⇐ = dom⇐₁ ; cod⇒ = cod⇒₁; square = square₁}) → begin
        F₁ (dom⇐₁ , cod⇒₁) ∘ F₁ (C.id , arr₁) ∘ dinatural.α dom₁                      ≈⟨ pullˡ (Equiv.sym homomorphism) ⟩
        F₁ (C.id C.∘ dom⇐₁ , cod⇒₁ C.∘ arr₁) ∘ dinatural.α dom₁                       ≈⟨ ([ F ]-decompose₁ ⟩∘⟨refl) ⟩
        (F₁ (C.id C.∘ dom⇐₁ , C.id) ∘ F₁ (C.id , cod⇒₁ C.∘ arr₁)) ∘ dinatural.α dom₁  ≈⟨ (F-resp-≈ (C.identityˡ , C.Equiv.refl) ⟩∘⟨refl ⟩∘⟨refl) ⟩
        (F₁ (dom⇐₁ , C.id) ∘ F₁ (C.id , cod⇒₁ C.∘ arr₁)) ∘ dinatural.α dom₁           ≈⟨ pullʳ (extranatural-commʳ dinatural) ⟩
        F₁ (dom⇐₁ , C.id) ∘ (F₁ (cod⇒₁ C.∘ arr₁ , C.id) ∘ dinatural.α cod)            ≈⟨ pullˡ (Equiv.sym homomorphism) ⟩
        F₁ ((cod⇒₁ C.∘ arr₁) C.∘ dom⇐₁ , C.id C.∘ C.id) ∘ dinatural.α cod             ≈⟨ (F-resp-≈ (C.assoc , C.identity²) ⟩∘⟨refl) ⟩
        F₁ (cod⇒₁ C.∘ arr₁ C.∘ dom⇐₁ , C.id) ∘ dinatural.α cod                        ≈⟨ (F-resp-≈ (square₁ , C.Equiv.refl) ⟩∘⟨refl) ⟩
        F₁ (arr , C.id) ∘ dinatural.α cod                                              ≈˘⟨ extranatural-commʳ dinatural ⟩
        F₁ (C.id , arr) ∘ dinatural.α dom   ∎             }
      }
    }

-- And a construction that builds a Wedge from a Cone (Twist F)
module _ (c : Cone (Twist F)) where
  open Cone c
  open DinaturalTransformation

  private
    fam : {A B : C.Obj} (f : A C.⇒ B) → N ⇒ F₀ (A , B)
    fam f = ψ record { arr = f }
    id² : {A B : C.Obj} (f : A C.⇒ B) → f C.∘ C.id C.∘ C.id C.≈ f
    id² f = C.∘-resp-≈ʳ C.identity² HR.○ C.identityʳ
      where
      module HR = C.HomReasoning

  Cone-to-Wedge : Wedge
  Cone-to-Wedge = record
    { E = N
    ; dinatural = dtHelper record
      { α = λ _ → fam C.id
      ; commute = λ f → begin
        F₁ (C.id , f) ∘ fam C.id ∘ id ≈⟨ pullˡ (Cone.commute c (mor⇒ (id² f))) ⟩
        ψ (record { arr = f }) ∘ id   ≈⟨ pushˡ (Equiv.sym (Cone.commute c (mor⇒ (C.identityˡ C.HomReasoning.○ C.identityˡ)))) ⟩
        F₁ (f , C.id) ∘ fam C.id ∘ id ∎
      }
    }
