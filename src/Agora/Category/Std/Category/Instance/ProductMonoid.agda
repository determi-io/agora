-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Category.Instance.ProductMonoid where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Data.Universe.Definition
open import Agora.Data.Product.Definition
open import Agora.Data.Lift.Definition
open import Agora.Algebra.Monoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Natural.Instance.Setoid
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Category.Instance.FiniteProductCategory
open import Agora.Category.Std.Category.Construction.Product
open import Agora.Category.Std.Category.Structured.FiniteProduct.As.Monoid
open import Agora.Category.Std.Category.Structured.FiniteProduct.Definition


-- | Here we show that 𝐂𝐚𝐭, the category of categories is a monoid with respect to
--   the product.


instance
  isMonoid:𝐂𝐚𝐭 : isMonoid (𝐂𝐚𝐭 𝑖)
  isMonoid:𝐂𝐚𝐭 = isMonoid:byHasFiniteProducts






-- ◌-𝐂𝐚𝐭 : 𝐂𝐚𝐭 𝑖
-- ◌-𝐂𝐚𝐭 = ′ Lift-Cat (𝟙 {ℓ₀}) ′

-- private
--   infixl 40 _⊗_
--   _⊗_ : 𝐂𝐚𝐭 𝑖 -> 𝐂𝐚𝐭 𝑖 -> 𝐂𝐚𝐭 𝑖
--   _⊗_ 𝒞 𝒟 = 𝒞 × 𝒟

--   lem-1 : {𝒞 : 𝐂𝐚𝐭 𝑖} -> ◌-𝐂𝐚𝐭 ⊗ 𝒞 ≅ 𝒞
--   lem-1 = π₁-𝐂𝐚𝐭 since P
--     where
--       P = {!!}


-- instance
--   isMonoid:𝐂𝐚𝐭 : isMonoid (𝐂𝐚𝐭 𝑖)
--   isMonoid:𝐂𝐚𝐭 = record
--                    { _⋆_         = _⊗_
--                    ; ◌           = ◌-𝐂𝐚𝐭
--                    ; unit-l-⋆    = lem-1
--                    ; unit-r-⋆    = {!!}
--                    ; assoc-l-⋆   = {!!}
--                    ; assoc-r-⋆   = {!!}
--                    ; _≀⋆≀_  = {!!}
--                    }





