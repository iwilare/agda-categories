{-# OPTIONS --without-K --safe #-}

-- the bicategory of Monads in a given bicategory K


open import Level
open import Data.Product using (_,_)

open import Categories.Bicategory
open import Categories.Category
open import Categories.Functor
import Categories.Bicategory.Extras as Bicat
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.Bicategory.Monad
import Categories.Morphism.Reasoning as MR


module Categories.Bicategory.Instance.Monads {o ℓ e t} (𝒞 : Bicategory o ℓ e t) where

open import Categories.Bicategory.Extras 𝒞 using (module Shorthands)
open Shorthands



record Monad⇒₁₀ (S T : Monad 𝒞) : Set (o ⊔ ℓ ⊔ e ⊔ t) where
  module T = Monad T
  module S = Monad S
  open Bicategory 𝒞
  field
    U : S.C ⇒₁ T.C
    τ : T.T ∘₁ U ⇒₂ U ∘₁ S.T
    --
    η-compat : τ ∘ᵥ (T.η ◁ U) ≈ ((U ▷ S.η) ∘ᵥ (ρ⇐ ∘ᵥ λ⇒))
    μ-compat : τ ∘ᵥ (T.μ ◁ U) ≈ (U ▷ S.μ ∘ᵥ (α⇒ ∘ᵥ τ ◁ S.T ∘ᵥ (α⇐ ∘ᵥ T.T ▷ τ ∘ᵥ α⇒)))

record Monad⇒₁₁ {S T : Monad 𝒞} (U U' : Monad⇒₁₀ S T) : Set (o ⊔ ℓ ⊔ e ⊔ t) where
  module T = Monad T
  module S = Monad S
  open Bicategory 𝒞
  module U = Monad⇒₁₀ U
  module U' = Monad⇒₁₀ U'
  field
    σ : U.U ⇒₂ U'.U
    τ-compat : U'.τ ∘ᵥ (T.T ▷ σ) ≈ (σ ◁ S.T) ∘ᵥ U.τ

Monad⇒₁ : Monad 𝒞 → Monad 𝒞 → Category (o ⊔ ℓ ⊔ e ⊔ t) (o ⊔ ℓ ⊔ e ⊔ t) {!   !}
Monad⇒₁ S T =
  let open Bicategory 𝒞
      module S = Monad S
      module T = Monad T in record
    { Obj = Monad⇒₁₀ S T
    ; _⇒_ = λ U V → Monad⇒₁₁ {S} {T} U V
    ; _≈_ = {!   !}
    ; id = λ { {A} → let module A = Monad⇒₁₀ A in
         record { σ = Bicategory.id₂ 𝒞
                ; τ-compat = begin _ ≈⟨ (refl⟩∘⟨ Bicat.▷id₂ 𝒞) ⟩
                                   _ ≈⟨ Bicat.id₂-comm 𝒞 ⟩
                                   _ ≈⟨ (hom.Equiv.sym (Bicat.▷id₂ 𝒞) ⟩∘⟨refl) ⟩
                                   _ ∎
                } }
    ; _∘_ = λ U V →
      let module U = Monad⇒₁₁ U
          module V = Monad⇒₁₁ V in record
      { σ = U.σ ∘ᵥ V.σ
      ; τ-compat = {!   !} -- λ {A} {B} {C} {D} {f} {g} {h} → {!   !}
      }
    ; assoc = {!   !}
    ; sym-assoc = {!   !}
    ; identityˡ = {!   !}
    ; identityʳ = {!   !}
    ; identity² = {!   !}
    ; equiv = {!   !}
    ; ∘-resp-≈ = {!   !}
    } where open Bicategory.hom.HomReasoning 𝒞

-- Monad⇒₂

Monads : Bicategory (o ⊔ ℓ ⊔ e ⊔ t) _ _ (o ⊔ ℓ ⊔ e ⊔ t)
Monads = record
  { enriched = record
    { Obj = Monad 𝒞
    ; hom = Monad⇒₁
    ; id = {!   !}
    ; ⊚ = {!   !}
    ; ⊚-assoc = {!   !}
    ; unitˡ = {!   !}
    ; unitʳ = {!   !}
    }
  ; triangle = {!   !}
  ; pentagon = {!   !}
  }
