
{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Core 
open import Categories.Functor
open import Categories.Category.Construction.Functors

module FOA {o ℓ e o' ℓ' e'} {params : Category o ℓ e} {carriers : Category o' ℓ' e'} {F : Functor params (Functors carriers carriers)} where

open import Level


open import Data.Product using (_,_; _×_; Σ)
open import Categories.Adjoint
open import Categories.Category.Product
open import Categories.Functor.Algebra
open import Categories.Category.Construction.F-Algebras
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism.Functors


record FOA-objects : Set (o ⊔ o' ⊔ ℓ') where
    constructor ⊲_,_⊳
    field
        param : Category.Obj params
        alg : F-Algebra ((Functor.F₀ F param))

open FOA-objects

reindex : {param' : Category.Obj params} (E : FOA-objects) (u : (params Category.⇒ param') (param E)) → F-Algebra ((Functor.F₀ F param'))
reindex {param'} E u = record 
  { A = F-Algebra.A (alg E) 
  ; α = F-Algebra.α (alg E) C.∘ NaturalTransformation.η (Functor.F₁ F u) (F-Algebra.A (alg E))
  } where module P = Category params
          module C = Category carriers

record FOA-arrows (E E' : FOA-objects) : Set (ℓ ⊔ ℓ' ⊔ e ⊔ e') where
    field
        u : (params Category.⇒ param E) (param E')
        f : F-Algebra-Morphism (alg E) (reindex E' u)

open FOA-arrows

FOA : Category (o ⊔ o' ⊔ ℓ') (ℓ ⊔ e ⊔ ℓ' ⊔ e') _ 
FOA = record
  { Obj = FOA-objects
  ; _⇒_ = λ E E' → FOA-arrows E E'
  ; _≈_ = λ {E} {E'} s t → (u s) P.≈ (u t) × (F-Algebra-Morphism.f (f s) C.≈ F-Algebra-Morphism.f (f t))
  ; id = λ { {⊲ param , alg ⊳} → record 
    { u = P.id 
    ; f = record 
      { f = C.id 
      ; commutes = {!   !} 
      } 
    } }
  ; _∘_ = λ { {⊲ param , alg ⊳} {⊲ param' , alg' ⊳} {⊲ param'' , alg'' ⊳} s t → record 
    { u = u s P.∘ u t 
    ; f = record 
      { f = F-Algebra-Morphism.f (f s) C.∘ F-Algebra-Morphism.f (f t) 
      ; commutes = {!   !} 
      } 
    }}
  ; assoc = P.assoc , C.assoc
  ; sym-assoc = P.sym-assoc , C.sym-assoc
  ; identityˡ = P.identityˡ , C.identityˡ
  ; identityʳ = P.identityʳ , C.identityʳ
  ; identity² = P.identity² , C.identity²
  ; equiv = record 
    { refl = P.Equiv.refl , C.Equiv.refl 
    ; sym = λ {(fst , snd) → P.Equiv.sym fst , C.Equiv.sym snd }
    ; trans = λ {(fst , snd) (fst₁ , snd₁) → 
      P.Equiv.trans fst fst₁ , C.Equiv.trans snd snd₁}
    }
  ; ∘-resp-≈ = {!   !}
  } where module P = Category params
          module C = Category carriers
          open F-Algebra-Morphism

