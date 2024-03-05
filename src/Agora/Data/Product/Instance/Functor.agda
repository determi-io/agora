-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Data.Product.Instance.Functor where

{-

open import Agora.Conventions
open import Agora.Data.Product.Definition
open import Agora.Data.Universe.Definition
open import Agora.Data.Universe.Instance.Category
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Construction.Product
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Limit.Specific.Product
open import Agora.Category.Std.Limit.Specific.Product.Instance.Functor

open import Agora.Data.Product.Definition
open import Agora.Data.Product.Instance.Product


instance
  isFunctor:×-𝒰 : isFunctor (𝐔𝐧𝐢𝐯 𝑖 ×-𝐂𝐚𝐭 𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) (λ₋ _×-𝒰_)
  isFunctor:×-𝒰 = isFunctor:⊓


-}

