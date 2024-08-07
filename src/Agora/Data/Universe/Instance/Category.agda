-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Data.Universe.Instance.Category where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Data.Universe.Definition


-- [Hide]
instance
  isSetoid:Function : ∀{A B : 𝒰 𝑖} -> isSetoid (A -> B)
  isSetoid:Function = isSetoid:byId
-- //

-- [Example]
-- | The type |𝒰| of types together with functions between
--   them is a category.
instance
  isCategory:𝒰 : isCategory (𝒰 𝑖)
  isCategory.Hom isCategory:𝒰 A B = A -> B
  isCategory.isSetoid:Hom isCategory:𝒰 = isSetoid:Function
  isCategory.id isCategory:𝒰 = id-𝒰
  isCategory._◆_ isCategory:𝒰 = _◆-𝒰_
  isCategory.unit-l-◆ isCategory:𝒰 = refl
  isCategory.unit-r-◆ isCategory:𝒰 = refl
  isCategory.unit-2-◆ isCategory:𝒰 = refl
  isCategory.assoc-l-◆ isCategory:𝒰 = refl
  isCategory.assoc-r-◆ isCategory:𝒰 = refl
  isCategory._◈_ isCategory:𝒰 p q = λ i -> p i ◆ q i
-- //

-- [Example]
-- | Another, more generic example is the following:
--   Given a category |𝒞|, inverting the direction
--   of all arrows produces a new category, called the
--   /opposite/ category, and denoted by |𝒞 ᵒᵖ|.

-- //

-- [Hide]
instance
  isSetoid:𝒰 : isSetoid (𝒰 𝑖)
  isSetoid:𝒰 = isSetoid:byCategory
-- //

