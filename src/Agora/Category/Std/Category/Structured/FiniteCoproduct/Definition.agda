-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Category.Structured.FiniteCoproduct.Definition where

open import Agora.Conventions
open import Agora.Setoid.Definition
-- open import Agora.Data.Fin.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition

FiniteCoproductCategory : ∀ 𝑖 -> 𝒰 _
FiniteCoproductCategory 𝑖 = Category 𝑖 :& hasFiniteCoproducts


