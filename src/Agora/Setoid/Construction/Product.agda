-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Setoid.Construction.Product where

open import Agora.Conventions
open import Agora.Data.Prop.Definition
open import Agora.Data.Product.Definition
open import Agora.Setoid.Definition
open import Agora.Setoid.Instance.Category

_×-𝐒𝐭𝐝_ : 𝐒𝐭𝐝 𝑖 -> 𝐒𝐭𝐝 𝑗 -> 𝐒𝐭𝐝 _
_×-𝐒𝐭𝐝_ A B = A × B


