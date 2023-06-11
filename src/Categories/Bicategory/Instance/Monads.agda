{-# OPTIONS --without-K --safe #-}

-- the bicategory of Monads in a given bicategory C, as defined in
-- `The formal theory of monads`. R. Street. Journal of Pure and Applied Algebra 2 (2): 149 - 168 (1972).


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

Monad⇒₁ : Monad 𝒞 → Monad 𝒞 → Category (o ⊔ ℓ ⊔ e ⊔ t) (o ⊔ ℓ ⊔ e ⊔ t) e
Monad⇒₁ S T =
  let module S = Monad S
      module T = Monad T in record
    { Obj = Monad⇒₁₀ S T
    ; _⇒_ = λ U V → Monad⇒₁₁ {S} {T} U V
    ; _≈_ = λ U V → let module U = Monad⇒₁₁ U
                        module V = Monad⇒₁₁ V
                        open Bicat 𝒞 in  U.σ ≈ V.σ
    ; id = λ { {A} → let module A = Monad⇒₁₀ A
                         open Bicat 𝒞 in
                         record { σ = Bicategory.id₂ 𝒞
                                ; τ-compat =
                                  begin (A.τ ∘ᵥ (A.T.T ▷ id₂)) ≈⟨ (refl⟩∘⟨ ▷id₂) ⟩
                                        (A.τ ∘ᵥ id₂)           ≈⟨ id₂-comm ⟩
                                        id₂ ∘ᵥ A.τ             ≈˘⟨ (id₂◁ ⟩∘⟨refl) ⟩
                                        (id₂ ◁ A.S.T) ∘ᵥ A.τ   ∎
                                } }
    ; _∘_ = λ U V →
      let open Bicat 𝒞
          module U = Monad⇒₁₁ U
          module V = Monad⇒₁₁ V
          in record
      { σ = U.σ ∘ᵥ V.σ
      ; τ-compat = {!!}
        -- begin (U.U'.τ ∘ᵥ (V.U'.T.T ▷ (U.σ ∘ᵥ V.σ))) ≈˘⟨ (refl⟩∘⟨ ∘ᵥ-distr-▷ )  ⟩
        --   (hom V.U'.S.C V.U'.T.C Category.∘ U.U'.τ)
        --     ((hom V.U'.S.C V.U'.T.C Category.∘ (V.U'.T.T ▷ U.σ))
        --     (V.U'.T.T ▷ V.σ)) ≈˘⟨ hom.assoc ⟩
        --   (hom V.U'.S.C V.U'.T.C Category.∘ (U.U'.τ ∘ᵥ (V.U'.T.T ▷ U.σ)))
        --     (V.U'.T.T ▷ V.σ) ≈⟨ (U.τ-compat ⟩∘⟨refl) ⟩
        --   (hom V.U'.S.C V.U'.T.C Category.∘
        --     (hom V.U'.S.C V.U'.T.C Category.∘ (U.σ ◁ V.U'.S.T)) V.U'.τ)
        --     (V.U'.T.T ▷ V.σ) ≈⟨ hom.assoc ⟩
        --   (hom V.U'.S.C V.U'.T.C Category.∘ (U.σ ◁ V.U'.S.T))
        --     (V.U'.τ ∘ᵥ (V.U'.T.T ▷ V.σ)) ≈⟨ (refl⟩∘⟨ V.τ-compat) ⟩
        --   (hom V.U'.S.C V.U'.T.C Category.∘ (U.σ ◁ V.U'.S.T))
        --     ((hom V.U'.S.C V.U'.T.C Category.∘ (V.σ ◁ V.U'.S.T)) V.U.τ) ≈˘⟨ hom.assoc ⟩
        --   (hom V.U'.S.C V.U'.T.C Category.∘
        --     ((U.σ ◁ V.U'.S.T) ∘ᵥ (V.σ ◁ V.U'.S.T)))
        --     V.U.τ ≈⟨ (∘ᵥ-distr-◁  ⟩∘⟨refl) ⟩
        --   ((U.σ ∘ᵥ V.σ) ◁ V.U'.S.T) ∘ᵥ V.U.τ ∎
      -- U.U'.τ ∘ᵥ V.U'.T.T ▷ (U.σ ∘ᵥ V.σ) ≈ (U.σ ∘ᵥ V.σ) ◁ V.U'.S.T ∘ᵥ V.U.τ
      }
    ; assoc = λ {A} {B} {C} {D} {U} {V} {W} →
      let module U = Monad⇒₁₁ U
          module V = Monad⇒₁₁ V
          module W = Monad⇒₁₁ W
          open Bicat 𝒞 in hom.assoc
    ; sym-assoc = λ {A} {B} {C} {D} {U} {V} {W} →
      let module U = Monad⇒₁₁ U
          module V = Monad⇒₁₁ V
          module W = Monad⇒₁₁ W
          open Bicat 𝒞 in hom.sym-assoc
    ; identityˡ = λ {A} {B} {U} →
      let module U = Monad⇒₁₁ U
          open Bicat 𝒞 in hom.identityˡ
    ; identityʳ = λ {A} {B} {U} →
      let module U = Monad⇒₁₁ U
          open Bicat 𝒞 in hom.identityʳ
    ; identity² = λ {A} → let open Bicat 𝒞 in hom.identity²
    ; equiv = let open Bicat 𝒞 in record
      { refl = hom.Equiv.refl
      ; sym = hom.Equiv.sym
      ; trans = hom.Equiv.trans
      }
    ; ∘-resp-≈ = let open Bicat 𝒞 in hom.∘-resp-≈
    } where open Bicategory.hom.HomReasoning 𝒞

-- Monad⇒₂
Monads : Bicategory (o ⊔ ℓ ⊔ e ⊔ t) _ _ (o ⊔ ℓ ⊔ e ⊔ t)
Monads = record
  { enriched = record
    { Obj = Monad 𝒞
    ; hom = Monad⇒₁
    ; id = let open Bicat 𝒞
               open Bicategory.hom.HomReasoning 𝒞 in record
             { F₀ = λ T →
               record { U = id₁
                      ; τ = ? -- λ⇐ ∘ᵥ ρ⇒
                      ; η-compat =  {!!}
                        -- begin {!!} ≈⟨ hom.assoc ⟩
                        --    {!   !} ≈⟨ refl⟩∘⟨ ρ⇒-∘ᵥ-◁ ⟩
                        --    {!   !} ≈⟨ hom.sym-assoc ⟩
                        --    {!   !} ≈˘⟨ ▷-∘ᵥ-λ⇐  ⟩∘⟨refl ⟩
                        --    {!   !} ≈⟨ hom.assoc ⟩
                        --    {!   !} ≈⟨ (refl⟩∘⟨ {!!} ) ⟩
                        --    {!   !} ≈⟨ (refl⟩∘⟨ {!!} ) ⟩
                        --    {!   !} ∎
                      -- (λ⇐ ∘ᵥ ρ⇒) ∘ᵥ η A₁ ◁ id₁ = (id₁ ▷ η A₁ ∘ᵥ ρ⇐ ∘ᵥ λ⇒)
                      ; μ-compat = begin {!   !} ≈⟨ {!   !} ⟩
                                         {!   !} ≈⟨ {!   !} ⟩
                                         {!   !} ∎
                      }
             ; F₁ = λ {C} {D} f →
               record { σ = id₂
                      ; τ-compat =
                        begin {!   !} ≈⟨ hom.assoc ⟩
                              {!   !} ≈⟨ hom.Equiv.sym ▷-∘ᵥ-λ⇐ ⟩
                              -- {!   !} ≈⟨ {!   !} ⟩
                              -- {!   !} ≈⟨ {!   !} ⟩
                              -- {!   !} ≈⟨ {!   !} ⟩
                              -- {!   !} ≈⟨ {!   !} ⟩
                              {!   !} ≈⟨ {!   !} ⟩
                              {!   !} ∎
                      }
             ; identity = {!!}
             ; homomorphism = {!!}
             ; F-resp-≈ = {!!}
             }
    ; ⊚ = {!!}
    ; ⊚-assoc = {!   !}
    ; unitˡ = {!   !}
    ; unitʳ = {!   !}
    }
  ; triangle = {!   !}
  ; pentagon = {!   !}
  } -- where open Bicategory.hom.HomReasoning 𝒞
