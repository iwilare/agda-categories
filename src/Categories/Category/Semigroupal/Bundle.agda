{-# OPTIONS --without-K --safe #-}

-- Bundled version of Semigroupal Category
module Categories.Category.Semigroupal.Bundle where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Semigroupal.Core using (Semigroupal)
-- open import Categories.Category.Semigroupal.Braided using (Braided)
-- open import Categories.Category.Semigroupal.Symmetric using (Symmetric)

record SemigroupalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U        : Category o ℓ e
    semigroupal : Semigroupal U


-- TODO: decomment after creating all the missing modules
--   open Category U public
--   open Semigroupal monoidal public

-- record BraidedSemigroupalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
--   field
--     U         : Category o ℓ e
--     monoidal  : Semigroupal U
--     braided   : Braided monoidal

--   monoidalCategory : SemigroupalCategory o ℓ e
--   monoidalCategory = record { U = U ; monoidal = monoidal }

--   open Category U public
--   open Braided braided public

-- record SymmetricSemigroupalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
--   field
--     U         : Category o ℓ e
--     monoidal  : Semigroupal U
--     symmetric : Symmetric monoidal

--   open Category U public
--   open Symmetric symmetric public

--   braidedSemigroupalCategory : BraidedSemigroupalCategory o ℓ e
--   braidedSemigroupalCategory = record
--     { U        = U
--     ; monoidal = monoidal
--     ; braided  = braided
--     }

--   open BraidedSemigroupalCategory braidedSemigroupalCategory public
--     using (monoidalCategory)
