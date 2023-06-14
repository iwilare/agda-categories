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

module Categories.Bicategory.Instance.MonadsDue {o ℓ e t} (𝒞 : Bicategory o ℓ e t) where

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
Category.Obj (Monad⇒₁ S T) = Monad⇒₁₀ S T
Category._⇒_ (Monad⇒₁ S T) = λ U V → Monad⇒₁₁ {S} {T} U V
Category._≈_ (Monad⇒₁ S T) = λ U V →
  let module U = Monad⇒₁₁ U
      module V = Monad⇒₁₁ V
      open Bicat 𝒞 in  U.σ ≈ V.σ
Category.id (Monad⇒₁ S T) {A} =
  record { σ = Bicategory.id₂ 𝒞
         ; τ-compat = let module A = Monad⇒₁₀ A
                          open Bicat 𝒞 in
         begin (A.τ ∘ᵥ (A.T.T ▷ id₂)) ≈⟨ (refl⟩∘⟨ ▷id₂) ⟩
                 (A.τ ∘ᵥ id₂)           ≈⟨ id₂-comm ⟩
                 id₂ ∘ᵥ A.τ             ≈˘⟨ (id₂◁ ⟩∘⟨refl) ⟩
                 (id₂ ◁ A.S.T) ∘ᵥ A.τ   ∎
         } where open Bicategory.hom.HomReasoning 𝒞
Category._∘_ (Monad⇒₁ S T) U V =
  record { σ = let open Bicat 𝒞
                   module U = Monad⇒₁₁ U
                   module V = Monad⇒₁₁ V
                   in U.σ ∘ᵥ V.σ
         ; τ-compat =
           let open Bicat 𝒞
               module U = Monad⇒₁₁ U
               module V = Monad⇒₁₁ V in
                       begin (U.U'.τ ∘ᵥ (V.U'.T.T ▷ (U.σ ∘ᵥ V.σ))) ≈˘⟨ (refl⟩∘⟨ ∘ᵥ-distr-▷ )  ⟩
          (hom V.U'.S.C V.U'.T.C Category.∘ U.U'.τ)
            ((hom V.U'.S.C V.U'.T.C Category.∘ (V.U'.T.T ▷ U.σ))
            (V.U'.T.T ▷ V.σ)) ≈˘⟨ hom.assoc ⟩
          (hom V.U'.S.C V.U'.T.C Category.∘ (U.U'.τ ∘ᵥ (V.U'.T.T ▷ U.σ)))
            (V.U'.T.T ▷ V.σ) ≈⟨ (U.τ-compat ⟩∘⟨refl) ⟩
          (hom V.U'.S.C V.U'.T.C Category.∘
            (hom V.U'.S.C V.U'.T.C Category.∘ (U.σ ◁ V.U'.S.T)) V.U'.τ)
            (V.U'.T.T ▷ V.σ) ≈⟨ hom.assoc ⟩
          (hom V.U'.S.C V.U'.T.C Category.∘ (U.σ ◁ V.U'.S.T))
            (V.U'.τ ∘ᵥ (V.U'.T.T ▷ V.σ)) ≈⟨ (refl⟩∘⟨ V.τ-compat) ⟩
          (hom V.U'.S.C V.U'.T.C Category.∘ (U.σ ◁ V.U'.S.T))
            ((hom V.U'.S.C V.U'.T.C Category.∘ (V.σ ◁ V.U'.S.T)) V.U.τ) ≈˘⟨ hom.assoc ⟩
          (hom V.U'.S.C V.U'.T.C Category.∘
            ((U.σ ◁ V.U'.S.T) ∘ᵥ (V.σ ◁ V.U'.S.T)))
            V.U.τ ≈⟨ (∘ᵥ-distr-◁  ⟩∘⟨refl) ⟩
          ((U.σ ∘ᵥ V.σ) ◁ V.U'.S.T) ∘ᵥ V.U.τ ∎
         } where open Bicategory.hom.HomReasoning 𝒞
Category.assoc (Monad⇒₁ S T) = let open Bicat 𝒞 in hom.assoc
Category.sym-assoc (Monad⇒₁ S T) = let open Bicat 𝒞 in hom.sym-assoc
Category.identityˡ (Monad⇒₁ S T) = let open Bicat 𝒞 in hom.identityˡ
Category.identityʳ (Monad⇒₁ S T) = let open Bicat 𝒞 in hom.identityʳ
Category.identity² (Monad⇒₁ S T) = let open Bicat 𝒞 in hom.identity²
Category.equiv (Monad⇒₁ S T) = let open Bicat 𝒞 in record
      { refl = hom.Equiv.refl
      ; sym = hom.Equiv.sym
      ; trans = hom.Equiv.trans
      }
Category.∘-resp-≈ (Monad⇒₁ S T) = let open Bicat 𝒞 in hom.∘-resp-≈




-- Monad⇒₂
Monads : Bicategory (o ⊔ ℓ ⊔ e ⊔ t) (o ⊔ ℓ ⊔ e ⊔ t) e {!   !}
Bicategory.enriched Monads = record
  { Obj = Monad 𝒞
  ; hom = Monad⇒₁
  ; id = λ {T} → let open Bicat 𝒞
                     open Bicategory.hom.HomReasoning 𝒞 in {!   !}
  ; ⊚ = record
    { F₀ = λ (f , g) → let module f = Monad⇒₁₀ f
                           module g = Monad⇒₁₀ g in
                             record { U = f.U ∘₁ g.U
                                    ; τ = {!   !}
                                    ; η-compat = {!   !}
                                    ; μ-compat = {!   !} }
    ; F₁ = λ (x , y) → {!   !}
    ; identity = {!   !}
    ; homomorphism = {!   !}
    ; F-resp-≈ = {!   !}
    }
  ; ⊚-assoc = {!   !}
  ; unitˡ = {!   !}
  ; unitʳ = {!   !}
  } where open Bicat 𝒞
          open Bicategory.hom.HomReasoning 𝒞
Bicategory.triangle Monads = {!   !}
Bicategory.pentagon Monads = {!   !}

{-


-- Monad⇒₂
Monads : Bicategory (o ⊔ ℓ ⊔ e ⊔ t) _ _ (o ⊔ ℓ ⊔ e ⊔ t)
Monads = record
  { enriched = record
    { Obj = Monad 𝒞
    ; hom = Monad⇒₁
    ; id = λ {T} → let open Bicat 𝒞
                       open Bicategory.hom.HomReasoning 𝒞 in record
             { F₀ = λ C →
               record { U = id₁
                      ; τ =  λ⇐ ∘ᵥ ρ⇒
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
-}