open import Level
open import Categories.Category
open import Categories.Functor renaming (id to idF)
open Categories.Functor.Functor
import Categories.Morphism.Reasoning as MR

module XMoore {o l e} {C : Category o l e} {X : Functor C C} (O : Category.Obj C) where

open Category C
open HomReasoning
open MR C
module X = Functor X

record XMooreObj : Set (o ⊔ l) where
  field
    E : Obj
    d : X.F₀ E ⇒ E
    s : E ⇒ O

open XMooreObj

record XMoore⇒ (A B : XMooreObj) : Set (o ⊔ l ⊔ e) where
  private
    module A = XMooreObj A
    module B = XMooreObj B
  field
    hom    : A.E ⇒ B.E
    comm-d : hom ∘ A.d ≈ B.d ∘ X.₁ hom
    comm-s : A.s ≈ B.s ∘ hom

open XMoore⇒

_⊚_ : {A B C : XMooreObj} → XMoore⇒ B C → XMoore⇒ A B → XMoore⇒ A C
_⊚_ {A} {B} {C} g f = record
  { hom = hom g ∘ hom f
  ; comm-d = begin
               (g.hom ∘ f.hom) ∘ d A       ≈⟨ pullʳ f.comm-d ⟩
               g.hom ∘ d B ∘ X.₁ f.hom     ≈⟨ extendʳ g.comm-d ⟩
               d C ∘ X.₁ g.hom ∘ X.₁ f.hom ≈⟨ refl⟩∘⟨ Equiv.sym X.homomorphism ⟩
               d C ∘ X.₁ (g.hom ∘ f.hom)   ∎
  ; comm-s = begin
               s A                 ≈⟨ f.comm-s ⟩
               s B ∘ f.hom         ≈⟨ pushˡ g.comm-s ⟩
               s C ∘ g.hom ∘ f.hom ∎
  } where module f = XMoore⇒ f
          module g = XMoore⇒ g

XMoore : Category (o ⊔ l) (o ⊔ l ⊔ e) e
XMoore = record
  { Obj = XMooreObj
  ; _⇒_ = XMoore⇒
  ; _≈_ = λ f g → hom f ≈ hom g
  ; id = λ { {A} → record
    { hom = id
    ; comm-d = begin
                 id ∘ d A ≈⟨ identityˡ ⟩
                 d A ≈˘⟨ MR.elimʳ C (Functor.identity X) ⟩
                 d A ∘ X.₁ id ∎
    ; comm-s = Equiv.sym identityʳ
    }}
  ; _∘_ = _⊚_
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈ = ∘-resp-≈
  } where open HomReasoning

-- if X is left adjoint, and C has pullbacks, then XMach has products (and then equalizers)

import Categories.Category.Complete
open import Categories.Category.Complete using (Complete)
open import Categories.Category.BinaryProducts
open import Categories.Object.Product.Indexed
open import Categories.Diagram.Pullback
open import Categories.Adjoint
open import Data.Nat
open import Relation.Binary.PropositionalEquality

module _ {R : Functor C C} (adj : X ⊣ R) {complete : ∀ {o ℓ e} → Complete o ℓ e C} where

  open import Categories.Object.Product.Indexed.Properties C
  open import Categories.Diagram.Pullback.Limit C

  module R = Functor R

  open Adjoint adj

  _^_$_ : Functor C C → ℕ → Obj → Obj
  F ^ zero  $ O = O
  F ^ suc n $ O = Functor.₀ F (F ^ n $ O)

  R∞ : IndexedProductOf C (R ^_$ O)
  R∞ = Complete⇒IndexedProductOf {i = 0ℓ} complete {I = ℕ} (R ^_$ O)

  module R∞ = IndexedProductOf R∞

  Rδ : (A : XMooreObj) (i : ℕ) → E A ⇒ R ^ i $ O
  Rδ A zero = s A
  Rδ A (suc i) = Ladjunct (Rδ A i ∘ d A)



  extractBehaviour : (A : XMooreObj)
                   → E A ⇒ R∞.X
  extractBehaviour A = R∞.⟨ Rδ A ⟩

  BinaryProducts-XMoore : BinaryProducts (XMoore)
  BinaryProducts-XMoore = record
    { product = λ { {A} {B} →
        let module A = XMooreObj A
            module B = XMooreObj B
            module P = Pullback (complete⇒pullback complete (extractBehaviour A) (extractBehaviour B))

          in record
          { A×B = record
            { E = P.P
            ; d = P.universal {X.F₀ P.P} {A.d ∘ X.₁ P.p₁} {B.d ∘ X.₁ P.p₂} {!  !}
            ; s = R∞.π 0 ∘ P.diag
            }
          ; π₁ = record
            { hom = P.p₁
            ; comm-d = {!   !}
            ; comm-s = {!   !}
            }
          ; π₂ = record
            { hom = P.p₂
            ; comm-d = {!   !}
            ; comm-s = {!   !}
            }
          ; ⟨_,_⟩ = λ PA PB → record
            { hom = {!   !}
            ; comm-d = {!   !}
            ; comm-s = {!   !}
            }
          ; project₁ = {!   !}
          ; project₂ = {!   !}
          ; unique = {!   !}
          }
      }
    }




{-
  open import Categories.Adjoint
  -- open import Categories.Category.BinaryProducts (Cartesian.products cartesian)
  open import Categories.Diagram.Pullback
  open import Categories.Diagram.Equalizer
  open import Categories.Object.Product
  open Product
  open Equalizer

  -- open Product

  module R = Functor R

  thmmmh : → (adj : X ⊣ R) → BinaryProducts (XMoore)
  thmmmh adj = record
    { product = λ { {A} {B} →
      let module A = XMooreObj A
          module B = XMooreObj B
          module P = Pullback (pullback (Ladjunct A.s) (Ladjunct B.s)) in record
        { A×B = record
          { E = P.P
          ; d = P.universal {X.F₀ P.P} {A.d ∘ X.₁ P.p₁} {B.d ∘ X.₁ P.p₂}
            (begin (R.₁ A.s ∘ unit.η A.E) ∘ A.d ∘ X.₁ P.p₁
                     ≈⟨ assoc ⟩
                   R.₁ A.s ∘ unit.η A.E ∘ A.d ∘ X.₁ P.p₁
                     ≈⟨ refl⟩∘⟨ MR.extendʳ C (unit.commute _) ⟩
                   R.₁ A.s ∘ R.₁ (X.₁ A.d) ∘ unit.η (X.F₀ A.E) ∘ X.₁ P.p₁
                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unit.commute _ ⟩
                   R.₁ A.s ∘ R.₁ (X.₁ A.d) ∘ R.₁ (X.₁ (X.F₁ P.p₁)) ∘ unit.η (X.F₀ P.P)
                     ≈⟨ {!   !} ⟩
                   {!   !} ≈⟨ {!   !} ⟩
                   {!   !} ≈⟨ {!   !} ⟩
                   {!   !} ≈⟨ {!   !} ⟩
                   (R.₁ B.s ∘ unit.η B.E) ∘ B.d ∘ X.₁ P.p₂ ∎)
          -- XP --> XRO --> O
          ; s = Radjunct P.diag
          }
        ; π₁ = record { hom = P.p₁
                      ; comm-d = {!   !}
                      ; comm-s = {!   !}
                      }
        ; π₂ = record { hom = P.p₂
                      ; comm-d = {!   !} ; comm-s = {!   !} }
        ; ⟨_,_⟩ = {!   !}
        ; project₁ = {!   !}
        ; project₂ = {!   !}
        ; unique = {!   !}
        }}
    } where open Adjoint adj
            open HomReasoning
-}
