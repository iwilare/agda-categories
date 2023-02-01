open import Level
open import Categories.Category
open import Categories.Functor renaming (id to idF)
open Categories.Functor.Functor
open import Data.Unit
open import Data.Product
open import Categories.Category.Construction.Comma
open import Categories.Functor.Algebra
open import Categories.Category.Construction.F-Algebras
import Categories.Morphism.Reasoning as MR

module Moore.Adjoints {o l e} {C : Category o l e} {X : Functor C C} (O : Category.Obj C) where

open import Categories.Category.Slice C
open import Categories.Adjoint
open import XMoore {o} {l} {e} {C} {X} O
open Category C
open HomReasoning
open Equiv
pattern * = lift Data.Unit.tt

-- behaviour functor
B : Functor XMoore (X ↘ O)
B = record
  { F₀ = λ { (xobj E d s) → record { f = s ∘ d } }
  ; F₁ = λ { {xobj E d s} {xobj F d' s'} (xarr g dc sc) → record
    { g = g
    ; h = *
    ; commute = begin _ ≈⟨ identityˡ ○ sc ⟩∘⟨refl ⟩
                      _ ≈⟨ MR.pullʳ C dc ○ sym-assoc ⟩
                      _ ∎
    }}
  ; identity = refl , *
  ; homomorphism = refl , *
  ; F-resp-≈ = λ x → x , *
  }

-- in order to find a left adjoint to B we first have to define
-- an adjunction between Alg(X) and C: XMre has functors
-- Alg(X) <-pAlg- XMre -pSlice-> X/O
pAlg : Functor XMoore (F-Algebras X)
pAlg = record
  { F₀ = λ {(xobj E d _) → record { A = E ; α = d }}
  ; F₁ = λ {(xarr f cd _) → record { f = f ; commutes = cd }}
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ x → x
  }

pSlice : Functor XMoore (Slice O)
pSlice = record
  { F₀ = λ {(xobj E _ s) → sliceobj s}
  ; F₁ = λ {(xarr f _ cs) → slicearr {h = f} (Equiv.sym cs) }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ x → x
  }

forget : Functor (F-Algebras X) C
forget = record
  { F₀ = F-Algebra.A
  ; F₁ = F-Algebra-Morphism.f
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ x → x
  }

postulate
  free : Functor C (F-Algebras X)
  ad : free ⊣ forget

module free = Functor free
open F-Algebra

-- L : Functor (X ↘ O) XMoore
-- L = record
--   { F₀ = λ { record { α = Z ; β = β ; f = f } →
--       xobj (A (free.F₀ Z)) (α {F = X} (free.F₀ Z)) {!   !}}
--   ; F₁ = {!   !}
--   ; identity = {!   !}
--   ; homomorphism = {!   !}
--   ; F-resp-≈ = {!   !}
--   }

-- thm : L ⊣ B
-- thm = {!   !}