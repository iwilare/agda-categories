open import Level
open import Categories.Category
open import Categories.Functor renaming (id to idF)
open Categories.Functor.Functor
import Categories.Morphism.Reasoning as MR

module Linears.Bicategory {u l e} {C : Category u l e} where

open import Data.Product using (_,_)
open import Categories.Category


open Category C

record LinObj (A B : Obj)  : Set (u ⊔ l ⊔ e) where
  field
    ϕ : A ⇒ B
    S : Obj
    i : A ⇒ S
    m : S ⇒ S
    o : S ⇒ B
    ϕ≈out∘mid∘in : ϕ ≈ o ∘ m ∘ i

open LinObj

record LinMor {A B : Obj} (X Y : LinObj A B) : Set (u ⊔ l ⊔ e) where
  field
    f : A ⇒ A
    g : B ⇒ B
    h : S X ⇒ S Y
    --
