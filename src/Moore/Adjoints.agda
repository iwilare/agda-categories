open import Level
open import Categories.Category
open import Categories.Functor renaming (id to idF)
open Categories.Functor.Functor
open import Data.Unit
open import Data.Product
open import Categories.Category.Construction.Comma
open import Categories.Functor.Algebra
open import Categories.Category.Construction.F-Algebras
open import Categories.NaturalTransformation
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

module forget = Functor forget

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
import Categories.Morphism.Reasoning as MR
import Function as Fun

module _ {R : Functor C C} (adj : X ⊣ R) {complete : ∀ {o ℓ e} → Complete o ℓ e C}
   {allIndexedPullbacks : ∀ i → AllPullbacksOf C i}
   (free : Functor C (F-Algebras X))
   (Free⊣Forget : free ⊣ forget)
   where

  module free = Functor free

  module Free⊣Forget = Adjoint Free⊣Forget

  open Pollo adj {complete = complete} {allIndexedPullbacks = allIndexedPullbacks}

  open MR C

  slaicia : Functor XMoore (Slice R∞.X)
  slaicia = record
    { F₀ = λ { A → sliceobj (F-Algebra-Morphism.f ((Free⊣Forget.Radjunct (behaviour A)))) }
    ; F₁ = λ { F → slicearr {! Equiv.sym (commute-behaviour F)  !} } --slicearr (Equiv.sym (commute-behaviour F)) }
    ; identity = {!   !} --Equiv.refl --refl
    ; homomorphism = {!   !} --Equiv.refl --refl
    ; F-resp-≈ = {!   !} --Fun.id
    }

  o∞ : F-Algebra X
  o∞ = record
    { A = R∞.X
    ; α = d∞
    }

{-
  L : Functor (Slice (forget.₀ o∞)) XMoore
  L = record
    { F₀ = λ { (sliceobj {A} arr)  → record
      { E = forget.₀ (free.₀ A)
      ; d = F-Algebra.α (free.₀ A)
      ; s = R∞.π 0 ∘ F-Algebra-Morphism.f (Free⊣Forget.Radjunct {A = A} {B = o∞} arr)
      } }
    ; F₁ = λ { Test@(slicearr {arr} △) → record
      { hom = F-Algebra-Morphism.f (free.₁ arr)
      ; comm-d = F-Algebra-Morphism.commutes (free.₁ arr)
      ; comm-s =
      begin
        R∞.π 0 ∘ F-Algebra-Morphism.f {!   !} --((F-Algebras X) [ {! Category.id (F-Algebras X)  !} ∘ {!   !} ])
          ≈⟨ refl⟩∘⟨ pushˡ (Equiv.sym identityˡ) ⟩
        R∞.π 0 ∘ F-Algebra-Morphism.f {!   !} --((F-Algebras X) [ Free⊣Forget.Radjunct {!  F-Algebra.α (free.₀ _) !} ∘ free.₁ arr ])
          ≈⟨ refl⟩∘⟨ Equiv.sym (Adjoint.Radjunct-square Free⊣Forget _ _ _ (Category.id (F-Algebras X)) (△ ○ Equiv.sym identityˡ)) ⟩
        R∞.π 0 ∘ F-Algebra-Morphism.f {! Free⊣Forget.counit.η _  !} ∘ F-Algebra-Morphism.f (free.₁ arr)
          ≈⟨ sym-assoc ⟩
        (R∞.π 0 ∘ F-Algebra-Morphism.f {!   !} {-(Adjoint.Radjunct Free⊣Forget ?)-}) ∘ F-Algebra-Morphism.f (free.₁ arr) ∎
      } }
    ; identity     = free.identity
    ; homomorphism = free.homomorphism
    ; F-resp-≈     = free.F-resp-≈
    }
  module L = Functor L

  module _ (A : SliceObj R∞.X) where
    private module A = SliceObj A

    mister : behaviour (L.₀ A) ≈ F-Algebra-Morphism.f (Adjoint.Radjunct Free⊣Forget A.arr)
    mister = begin
      behaviour (₀ L A)
        ≈⟨ {!   !} ⟩
      {!   !}
        ≈⟨ {!   !} ⟩
      F-Algebra-Morphism.f (Adjoint.Radjunct Free⊣Forget A.arr)
        ∎

  -- the following is a proof that slaicia is a left adjoint to B
  -- (which is a right adjoint to R)
  -- the proof is a bit long, but it is not too complicated
  adj-slaicia : L ⊣ slaicia
  adj-slaicia = record
    { unit = ntHelper record
      { η = λ A →
       let module A = SliceObj A in
              slicearr {_} {h = Free⊣Forget.unit.η A.Y}
                ({!   !} ⟩∘⟨refl ○ Free⊣Forget.LRadjunct≈id {f = A.arr})
              --({!   !} ○ Free⊣Forget.LRadjunct≈id {f = A.arr})
              --(begin
              --  {!  d∞ ∘ ? !} ≈⟨ {!   !} ⟩
              --  {!   !} ∎)
      ; commute = {!   !}
      }
    ; counit = {!   !}
    ; zig = {!   !}
    ; zag = {!   !}
    }
-}
{-

d∞


Categories.Diagram.Cone.Cone⇒.arr
(IsTerminal.!
 (Terminal.⊤-is-terminal
  (Categories.Diagram.Limit.Limit.terminal
   (complete
    (Categories.Category.Construction.StrictDiscrete.lift-func C
     (R ^_$ O)
     ∘F
     Categories.Category.Lift.unliftF Level.zero Level.zero Level.zero
     (Categories.Category.Construction.StrictDiscrete.Discrete ℕ))))))
-}
