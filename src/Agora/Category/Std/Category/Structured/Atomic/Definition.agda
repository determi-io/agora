-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Category.Structured.Atomic.Definition where

open import Agora.Conventions hiding (_⊔_)
open import Agora.Setoid
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Category.Instance.2Category
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Structured.FiniteCoproduct.Definition
open import Agora.Category.Std.Limit.Cone.Colimit.Preservation
open import Agora.Category.Std.Functor.Representable2

--
-- Definition from https://nlab-pages.s3.us-east-2.amazonaws.com/nlab/show/atom
--

module _ {C : 𝒰 𝑖} {{_ : isCategory {𝑖₁} C}} (𝑗 : 𝔏 ^ 3) where
  isAtom : (e : C) -> 𝒰 _
  isAtom e = preservesAllColimits (ℎ𝑜𝑚ᵒᵖ e) 𝑗






