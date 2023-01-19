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
open import Categories.Object.Terminal
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
  R∞ = Complete⇒IndexedProductOf {0ℓ} {0ℓ} {0ℓ} {0ℓ} complete {I = ℕ} (R ^_$ O)

  Rδ : (A : XMooreObj) (i : ℕ) → E A ⇒ R ^ i $ O
  Rδ A zero = s A
  Rδ A (suc i) = Ladjunct (Rδ A i ∘ d A)

  module R∞ = IndexedProductOf R∞

  behaviour : (A : XMooreObj) → E A ⇒ R∞.X
  behaviour A = R∞.⟨ Rδ A ⟩

  delta-from-behaviour : ∀ {A} → A ⇒ R∞.X → X.₀ A ⇒ A
  delta-from-behaviour behaviour = {!   !} -- Is this possible?

  Terminal-XMoore : Terminal XMoore
  Terminal-XMoore = record
    { ⊤ = record
      { E = R∞.X
      ; d = d∞
      ; s = R∞.π 0
      }
    ; ⊤-is-terminal = record
      { ! = λ {A} → let module A = XMooreObj A in record
        { hom = behaviour A
        ; comm-d =
            begin
              R∞.⟨ Rδ A ⟩ ∘ A.d
                ≈⟨ R∞.⟨⟩∘ (Rδ A) (d A) ⟩
              R∞.⟨ (λ i → Rδ A i ∘ A.d) ⟩
                ≈⟨ R∞.⟨⟩-cong _ _ pointwise-comm-d ⟩
              R∞.⟨ (λ i → (Radjunct (R∞.π (ℕ.suc i))) ∘ X.₁ (behaviour A)) ⟩
                ≈⟨ ⟺ (R∞.⟨⟩∘ _ (X.₁ (behaviour A))) ⟩
              d∞ ∘ X.₁ (behaviour A) ∎
        ; comm-s = ⟺ (R∞.commute (Rδ A) 0)
        }
      ; !-unique = λ {A} f → R∞.unique _ _ (uniqueness f)
      }
    } where
      d∞ : X.₀ R∞.X ⇒ R∞.X
      d∞ = R∞.⟨ (λ i → Radjunct (R∞.π (ℕ.suc i))) ⟩

      module _ {A : XMooreObj} where
        private module A = XMooreObj A

        module _ (f : XMoore⇒ A _) where
          private module f = XMoore⇒ f
          uniqueness : (i : ℕ) → R∞.π i ∘ f.hom ≈ Rδ A i
          uniqueness ℕ.zero = Equiv.sym f.comm-s
          uniqueness (ℕ.suc i) = begin
            R∞.π (ℕ.suc i) ∘ f.hom
              ≈⟨ introˡ zag ⟩
            (R.₁ (counit.η (R ^ i $ O)) ∘ unit.η _) ∘ R∞.π (ℕ.suc i) ∘ f.hom
              ≈⟨ assoc ⟩
            R.₁ (counit.η (R ^ i $ O)) ∘ unit.η _ ∘ R∞.π (ℕ.suc i) ∘ f.hom
              ≈⟨ refl⟩∘⟨ unit.commute _ ⟩
            R.₁ (counit.η (R ^ i $ O)) ∘ R.₁ (X.₁ (R∞.π (ℕ.suc i) ∘ f.hom)) ∘ unit.η _
              ≈⟨ pullˡ (Equiv.sym R.homomorphism) ⟩
            R.₁ (counit.η (R ^ i $ O) ∘ X.₁ (R∞.π (ℕ.suc i) ∘ f.hom)) ∘ unit.η _
              ≈⟨ R.F-resp-≈ (refl⟩∘⟨ X.homomorphism) ⟩∘⟨refl ⟩
            R.₁ (counit.η (R ^ i $ O) ∘ X.₁ (R∞.π (ℕ.suc i)) ∘ X.₁ f.hom) ∘ unit.η _
              ≈⟨ R.F-resp-≈ (extendʳ (Equiv.sym (R∞.commute _ i))) ⟩∘⟨refl ⟩
            R.₁ (R∞.π i ∘ d∞ ∘ X.₁ f.hom) ∘ unit.η _
              ≈⟨ R.F-resp-≈ (refl⟩∘⟨ Equiv.sym f.comm-d) ⟩∘⟨refl ⟩
            R.₁ (R∞.π i ∘ f.hom ∘ A.d) ∘ unit.η _
              ≈⟨ R.F-resp-≈ (pullˡ (uniqueness i)) ⟩∘⟨refl ⟩
            R.₁ (Rδ A i ∘ A.d) ∘ unit.η _
              ≈⟨ Equiv.refl ⟩
            Ladjunct (Rδ A i ∘ A.d) ∎

        pointwise-comm-d : (i : ℕ)
          → Rδ A i ∘ A.d
          ≈ Radjunct (R∞.π (ℕ.suc i)) ∘ X.₁ (behaviour A)
        pointwise-comm-d i = begin
          Rδ A i ∘ A.d ≈⟨ Equiv.sym (elimʳ zig) ⟩
          (Rδ A i ∘ A.d) ∘ counit.η (X.F₀ A.E) ∘ X.₁ (unit.η A.E) ≈⟨ Equiv.sym (extendʳ (counit.commute _)) ⟩
          counit.η (R ^ i $ O) ∘ X.₁ (R.₁ (Rδ A i ∘ A.d)) ∘ X.₁ (unit.η A.E) ≈⟨ refl⟩∘⟨ Equiv.sym X.homomorphism ⟩
          counit.η (R ^ i $ O) ∘ X.₁ (Ladjunct (Rδ A i ∘ A.d)) ≈⟨ refl⟩∘⟨ X.F-resp-≈ (Equiv.sym (R∞.commute _ (ℕ.suc i))) ⟩
          counit.η (R ^ i $ O) ∘ X.₁ (R∞.π (ℕ.suc i) ∘ R∞.⟨ Rδ A ⟩) ≈⟨ refl⟩∘⟨ X.homomorphism ⟩
          counit.η (R ^ i $ O) ∘ X.₁ (R∞.π (ℕ.suc i)) ∘ X.₁ R∞.⟨ Rδ A ⟩ ≈⟨ sym-assoc ⟩
          Radjunct (R∞.π (ℕ.suc i)) ∘ X.₁ R∞.⟨ Rδ A ⟩ ∎

  BinaryProducts-XMoore : BinaryProducts (XMoore)
  BinaryProducts-XMoore = record
    { product = λ { {A} {B} →
        let module A = XMooreObj A
            module B = XMooreObj B

            -- Pullback on i-step behaviour
            module Pi i = Pullback (complete⇒pullback complete (Rδ A i) (Rδ B i))

            -- Pullback on full behaviour
            module P∞ = Pullback (complete⇒pullback complete (behaviour A) (behaviour B))

            -- Product of pullbacks
            module Pall = IndexedProductOf (Complete⇒IndexedProductOf {0ℓ} {0ℓ} {0ℓ} {0ℓ} complete {I = ℕ} λ i → Pi.P i)

          in record
          { A×B = record
            { E = P∞.P
            ; d = Radjunct {!   !}
            {-
            P.universal {A = X.F₀ P.P} {A.d ∘ X.₁ P.p₁} {B.d ∘ X.₁ P.p₂}
                           (begin
           {!   !} ≈⟨ pullˡ (R∞.⟨⟩∘ {!   !} {!   !}) ⟩
           {!   !} ≈⟨ R∞.⟨⟩∘ {!   !} {!   !} ⟩
           {!   !} ≈⟨ R∞.⟨⟩-cong _ _ {!   !} ⟩
           {!   !} ≈˘⟨ R∞.⟨⟩∘ {!   !} {!   !} ⟩
           {!   !} ≈˘⟨ pullˡ (R∞.⟨⟩∘ {!   !} {!   !}) ⟩
           {!   !} ∎)
            -}
            ; s = R∞.π 0 ∘ P∞.diag
            }
          ; π₁ = record
            { hom = P∞.p₁
            ; comm-d = {!   !}
            ; comm-s = {!   !}
            }
          ; π₂ = record
            { hom = P∞.p₂
            ; comm-d = {!   !}
            ; comm-s = {!   !}
            }
          ; ⟨_,_⟩ = λ {C} PA PB →
            let module PA = XMoore⇒ PA
                module PB = XMoore⇒ PB in record
            { hom = P∞.universal {A = E C} {PA.hom} {PB.hom} (begin
               R∞.⟨ Rδ A ⟩ ∘ PA.hom ≈⟨ R∞.⟨⟩∘ _ _ ⟩
               R∞.⟨ (λ i → Rδ A i ∘ PA.hom) ⟩ ≈⟨ R∞.⟨⟩-cong _ _ (pointwiso PA PB) ⟩
               R∞.⟨ (λ i → Rδ B i ∘ PB.hom) ⟩ ≈˘⟨ R∞.⟨⟩∘ _ _ ⟩
               R∞.⟨ Rδ B ⟩ ∘ PB.hom ∎)
            ; comm-d = {! P∞.unique  !}
            ; comm-s = {!  PA.comm-s !}
            }
          ; project₁ = {!   !}
          ; project₂ = {!   !}
          ; unique = {!   !}
          }
      }
    } where
        module _ {A B : XMooreObj} where
          private
            module A = XMooreObj A
            module B = XMooreObj B
            module P = Pullback (complete⇒pullback complete (behaviour A) (behaviour B))

          private
            variable
              G : XMooreObj

          module _ (PA : XMoore⇒ G A) (PB : XMoore⇒ G B) where
            private
              module PA = XMoore⇒ PA
              module PB = XMoore⇒ PB

            pointwiso : (i : ℕ)
                      → Rδ A i ∘ PA.hom ≈ Rδ B i ∘ PB.hom
            pointwiso ℕ.zero = Equiv.sym PA.comm-s ○ PB.comm-s
            pointwiso (ℕ.suc i) = begin
               (R.F₁ (Rδ A i ∘ A.d) ∘ unit.η A.E) ∘ PA.hom
                 ≈⟨ pullʳ (unit.commute _) ⟩
               R.F₁ (Rδ A i ∘ A.d) ∘ R.F₁ (X.₁ PA.hom) ∘ unit.η (E G)
                 ≈⟨ pullˡ (Equiv.sym R.homomorphism) ⟩
               R.F₁ ((Rδ A i ∘ A.d) ∘ X.₁ PA.hom) ∘ unit.η (E G)
                 ≈⟨ R.F-resp-≈ (pullʳ (Equiv.sym PA.comm-d)) ⟩∘⟨refl ⟩
               R.F₁ (Rδ A i ∘ PA.hom ∘ d G) ∘ unit.η (E G)
                 ≈⟨ R.F-resp-≈ (extendʳ (pointwiso i)) ⟩∘⟨refl ⟩
               R.F₁ (Rδ B i ∘ PB.hom ∘ d G) ∘ unit.η (E G)
                 ≈˘⟨ R.F-resp-≈ (pullʳ (Equiv.sym PB.comm-d)) ⟩∘⟨refl ⟩
               R.F₁ ((Rδ B i ∘ B.d) ∘ X.₁ PB.hom) ∘ unit.η (E G)
                 ≈˘⟨ pullˡ (Equiv.sym R.homomorphism) ⟩
               R.F₁ (Rδ B i ∘ B.d) ∘ R.₁ (X.₁ PB.hom) ∘ unit.η (E G)
                 ≈˘⟨ pullʳ (unit.commute _) ⟩
               (R.F₁ (Rδ B i ∘ B.d) ∘ unit.η B.E) ∘ PB.hom ∎
