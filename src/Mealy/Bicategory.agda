{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Categories.Category
open import Categories.Bicategory
open import Categories.Functor renaming (id to idF)
open Categories.Functor.Functor
open import Categories.Functor.Construction.Constant
import Categories.Morphism.Reasoning as MR
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Object.Terminal

open import Categories.Category.Cartesian

open import Mealy

module Mealy.Bicategory {o l e} {C : Category o l e} {K : Cartesian C} where

module C = Category C
module K = Cartesian K
open C.HomReasoning
open MR C

open Terminal K.terminal
open BinaryProducts K.products

MealyBicategory : Bicategory {!   !} {!   !} {!   !} {!   !}
MealyBicategory = record
  { enriched = record
    { Obj = C.Obj
    ; hom = Mealy {C = C} {K = K}
    ; id = const (record
      { E = ⊤
      ; d = !
      ; s = π₂
      })
    ; ⊚ = {!   !}
    -- ^ 1-cell composition
    ; ⊚-assoc = {!   !}
    ; unitˡ = {!   !}
    ; unitʳ = {!   !}
    }
  ; triangle = {!   !}
  ; pentagon = {!   !}
  }
