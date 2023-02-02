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
  { F₀ = λ { A → let module A = XMooreObj A in record { f = A.s ∘ A.d } }
  ; F₁ = λ { F → let module F = XMoore⇒ F in record
    { g = F.hom
    ; h = *
    ; commute = begin _ ≈⟨ identityˡ ○ F.comm-s ⟩∘⟨refl ⟩
                      _ ≈⟨ MR.pullʳ C F.comm-d ○ sym-assoc ⟩
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
  { F₀ = λ { A → let module A = XMooreObj A in record { A = A.E ; α = A.d }}
  ; F₁ = λ { F → let module F = XMoore⇒ F in record { f = F.hom ; commutes = F.comm-d }}
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ x → x
  }

pSlice : Functor XMoore (Slice O)
pSlice = record
  { F₀ = λ { A → let module A = XMooreObj A in sliceobj A.s}
  ; F₁ = λ { F → let module F = XMoore⇒ F in slicearr {h = F.hom} (Equiv.sym F.comm-s) }
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

import Categories.Category.Complete
open import Categories.Category.Complete using (Complete)
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Category.Complete.Properties using (Complete⇒FinitelyComplete)
open import Categories.Category.BinaryProducts
open import Categories.Object.Product.Indexed
open import Categories.Object.Product
open import Categories.Diagram.Pullback.Indexed
open import Categories.Object.Terminal
open import Categories.Diagram.Pullback
open import Categories.Adjoint
open import Data.Nat
open import Relation.Binary.PropositionalEquality

module _ {R : Functor C C} (adj : X ⊣ R) {complete : ∀ {o ℓ e} → Complete o ℓ e C}
   {allIndexedPullbacks : ∀ i → AllPullbacksOf C i}
   where

  open Pollo adj {complete = complete} {allIndexedPullbacks = allIndexedPullbacks}

  slaicia : Functor XMoore (Slice R∞.X)
  slaicia = record
    { F₀ = λ { A → sliceobj (behaviour A) }
    ; F₁ = λ { F → slicearr (Equiv.sym (commute-behaviour F)) }
    ; identity = {!   !} --refl
    ; homomorphism = {!   !} --refl
    ; F-resp-≈ = {!   !} --λ x → x
    }
