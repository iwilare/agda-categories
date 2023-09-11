
open import Categories.Category.Core 
open import Level

module Categories.Adjoint.MaybeAdj {o l e} {C D : Category o l e} where

open import Categories.Functor
open import Categories.Functor.Hom
open import Categories.Functor.Properties
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Core
open import Categories.Adjoint
open import Categories.Adjoint.Properties
import Categories.Morphism.Reasoning as MR

open import Data.Sum.Base

private
  variable
    F : Functor C D 
    G : Functor D C 
    ad : F ⊣ G

private 
  module C = Category C 
  module D = Category D


open import Categories.Adjoint 
open import Categories.Adjoint.Equivalents 

open import Categories.Monad
open import Categories.Comonad

open import Categories.Adjoint.Construction.CoKleisli 
open import Categories.Adjoint.Construction.Kleisli 
open import  Categories.Category.Construction.Kleisli
open import  Categories.Category.Construction.CoKleisli

G' : Functor (Kleisli (adjoint⇒monad ad)) (CoKleisli (adjoint⇒comonad ad))
G' = {!   !}

-- T : Monad C 
-- T = {!  adjoint⇒monad {C = C} {D = D}  !} -- adjoint⇒monad ad

-- S : Comonad D 
-- S = {!   !} -- adjoint⇒comonad ad

F' : Functor (CoKleisli (adjoint⇒comonad ad)) (Kleisli (adjoint⇒monad  ad))
F' = {!   !}

duplo : (F : Functor C D) →  
    (G : Functor D C) → 
    (ad : F ⊣ G) → Category o l e
duplo F G ad = record
  { Obj = C.Obj ⊎ D.Obj
  ; _⇒_ = λ { (inj₁ P1) (inj₁ P2) → P1 C.⇒ M.F.F₀ P2
             ; (inj₁ P) (inj₂ N) → F.F₀ P D.⇒ N
             ; (inj₂ N) (inj₁ P) → G.F₀ N C.⇒ G.F₀ (F.F₀ P)
             ; (inj₂ N1) (inj₂ N2) → S.F.F₀ N1 D.⇒ N2 
             }
  ; _≈_ = λ { {inj₁ P1} {inj₁ P2} f g → f C.≈ g
            ; {inj₁ P} {inj₂ N} f g → f D.≈ g
            ; {inj₂ N} {inj₁ P} f g → f C.≈ g
            ; {inj₂ N1} {inj₂ N2} f g → f D.≈ g
            }
  ; id = λ { {inj₁ P} → NaturalTransformation.η ad.unit P
           ; {inj₂ N} → NaturalTransformation.η ad.counit N
           }
  ; _∘_ = λ { {inj₁ P1} {inj₁ P2} {inj₁ P3} f g → M.μ.η _ C.∘ M.F.F₁ f C.∘ g
            ; {inj₁ P1} {inj₁ P2} {inj₂ N1} f g → ad.Radjunct (G.F₁ f C.∘ g)
            ; {inj₁ P1} {inj₂ N1} {inj₁ P2} f g → f C.∘ ad.Ladjunct g
            ; {inj₁ P1} {inj₂ N1} {inj₂ N2} f g → f D.∘ S.F.F₁ g D.∘ F.F₁ (M.η.η _)
            ; {inj₂ N1} {inj₁ P1} {inj₁ P2} f g → M.μ.η _ C.∘ M.F.F₁ f C.∘ g
            ; {inj₂ N1} {inj₁ P1} {inj₂ N2} f g → f D.∘ NaturalTransformation.η ad.counit _ D.∘ F.F₁ g
            ; {inj₂ N1} {inj₂ N2} {inj₁ P1} f g → f C.∘ ad.Ladjunct g
            ; {inj₂ N1} {inj₂ N2} {inj₂ N3} f g → f D.∘ S.F.F₁ g D.∘ S.δ.η _
            }
  ; assoc = λ { {inj₁ P1} {inj₁ P2} {inj₁ P3} {inj₁ P4} {f} {g} {h} → let open C.HomReasoning 
                                                                          open MR C in begin {!   !} ≈⟨ C.sym-assoc ⟩ 
                                                                                             {!   !} ≈⟨ (refl⟩∘⟨ M.F.F-resp-≈ C.sym-assoc) ⟩∘⟨refl ⟩ 
                                                                                             {!   !} ≈⟨ ((refl⟩∘⟨ {! K.assoc  !}) ⟩∘⟨refl) ⟩ 
                                                                                             {!   !} ≈⟨ {!  !} ⟩ 
                                                                                             {!   !} ∎
              ; {inj₁ P1} {inj₁ P2} {inj₁ P3} {inj₂ N1} {f} {g} {h} → let open D.HomReasoning 
                                                                          open MR D in begin {!   !} ≈⟨ {!   !} ⟩  
                                                                                             {!   !} ≈⟨ {!   !} ⟩ 
                                                                                             {!   !} ∎
              ; {inj₁ P1} {inj₁ P2} {inj₂ N1} {inj₁ P3} {f} {g} {h} → let open C.HomReasoning 
                                                                          open MR C in {! begin ? ≈⟨ ? ⟩ ? ∎  !}
              ; {inj₁ P1} {inj₂ N1} {inj₁ P2} {inj₁ P3} {f} {g} {h} → let open C.HomReasoning 
                                                                          open MR C in {! begin ? ≈⟨ ? ⟩ ? ∎  !}
              ; {inj₁ P1} {inj₂ N1} {inj₂ N2} {inj₁ P2} {f} {g} {h} → let open C.HomReasoning 
                                                                          open MR C in {! begin ? ≈⟨ ? ⟩ ? ∎  !}
              ; {inj₂ N1} {inj₁ P1} {inj₁ P2} {inj₁ P3} {f} {g} {h} → let open C.HomReasoning 
                                                                          open MR C in {! begin ? ≈⟨ ? ⟩ ? ∎  !}
              ; {inj₂ N1} {inj₁ P1} {inj₁ P2} {inj₂ N2} {f} {g} {h} → let open C.HomReasoning 
                                                                          open MR C in {! begin ? ≈⟨ ? ⟩ ? ∎  !}
              ; {inj₂ N1} {inj₁ P1} {inj₂ N2} {inj₁ P2} {f} {g} {h} → let open C.HomReasoning 
                                                                          open MR C in {!  begin ? ≈⟨ ? ⟩ ? ∎ !}
              ; {inj₂ N1} {inj₂ N2} {inj₁ P1} {inj₁ P2} {f} {g} {h} → let open C.HomReasoning 
                                                                          open MR C in {! begin ? ≈⟨ ? ⟩ ? ∎  !}
              ; {inj₂ N1} {inj₂ N2} {inj₂ N3} {inj₁ P1} {f} {g} {h} → let open C.HomReasoning 
                                                                          open MR C in {! begin ? ≈⟨ ? ⟩ ? ∎  !}
              ; {inj₁ P1} {inj₁ P2} {inj₂ N1} {inj₂ N2} {f} {g} {h} → let open D.HomReasoning 
                                                                          open MR D in {! begin ? ≈⟨ ? ⟩ ? ∎  !}
              ; {inj₁ P1} {inj₂ N1} {inj₁ P2} {inj₂ N2} {f} {g} {h} → let open D.HomReasoning 
                                                                          open MR D in {!  begin ? ≈⟨ ? ⟩ ? ∎ !}
              ; {inj₁ P1} {inj₂ N1} {inj₂ N2} {inj₂ N3} {f} {g} {h} → let open D.HomReasoning 
                                                                          open MR D in {! begin ? ≈⟨ ? ⟩ ? ∎  !}
              ; {inj₂ N1} {inj₁ P1} {inj₂ N2} {inj₂ N3} {f} {g} {h} → let open D.HomReasoning 
                                                                          open MR D in {! begin ? ≈⟨ ? ⟩ ? ∎  !}
              ; {inj₂ N1} {inj₂ N2} {inj₁ P1} {inj₂ N3} {f} {g} {h} → let open D.HomReasoning 
                                                                          open MR D in {! begin ? ≈⟨ ? ⟩ ? ∎  !}
              ; {inj₂ N1} {inj₂ N2} {inj₂ N3} {inj₂ N4} {f} {g} {h} → Z.assoc {f = f} {g = g} {h = h}
              }
  ; sym-assoc = {!   !}
  ; identityˡ = λ { {inj₁ P1} {inj₁ P2} {f} → let open C.HomReasoning 
                                                  open MR C in C.sym-assoc ○ elimˡ M.identityˡ
                  ; {inj₂ N} {inj₁ P} {f} → let open C.HomReasoning 
                                                open MR C in C.sym-assoc ○ elimˡ M.identityˡ
                  ; {inj₁ P} {inj₂ N} {f} → let open D.HomReasoning 
                                                open MR D in begin _ ≈⟨ D.sym-assoc ⟩
                                                                   _ ≈⟨ (ad.counit.commute _ ⟩∘⟨refl) ⟩ 
                                                                   _ ≈⟨ D.assoc ⟩ 
                                                                   _ ≈⟨ elimʳ (Adjoint.zig ad) ⟩ 
                                                                   _ ∎
                  ; {inj₂ N1} {inj₂ N2} {f} → let open D.HomReasoning 
                                                  open MR D in begin _ ≈⟨ D.sym-assoc ⟩
                                                                     _ ≈⟨ ((ad.counit.commute _ ⟩∘⟨refl)) ⟩
                                                                     _ ≈⟨ D.assoc ⟩
                                                                     _ ≈⟨ elimʳ (Adjoint.zig ad) ⟩
                                                                     _ ∎
                  }
  ; identityʳ = λ { {A} {B} {f} → {!  !}}
  ; identity² = λ { {inj₁ x} → let open C.HomReasoning 
                                   open MR C in C.sym-assoc ○ elimˡ M.identityˡ
                  ; {inj₂ y} → let open D.HomReasoning 
                                   open MR D in  elimʳ S.identityˡ 
                  }
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  } where module F = Functor F 
          module G = Functor G
          module ad = Adjoint ad
          module M = Monad (adjoint⇒monad ad)
          module S = Comonad (adjoint⇒comonad ad)
          module K = Category (Kleisli (adjoint⇒monad  ad))
          module Z = Category (CoKleisli (adjoint⇒comonad ad)) 
          -- open C.HomReasoning
          -- open MR C

-- miracle : G' ⊣ F' 
-- miracle = ? 