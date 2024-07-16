-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Category.Structured.FiniteCoproduct.As.FiniteProduct where

open import Agora.Conventions hiding (_⊔_)
open import Agora.Setoid.Definition
open import Agora.Algebra.Monoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Opposite
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition
open import Agora.Category.Std.Limit.Specific.Coproduct.Instance.Product
open import Agora.Category.Std.Limit.Specific.Product


module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where
  instance
    hasProducts:ᵒᵖ : hasProducts (𝒞 ᵒᵖ)
    hasProducts._⊓_ hasProducts:ᵒᵖ = _⊔_
    hasProducts.isProduct:⊓ hasProducts:ᵒᵖ = it

    hasTerminal:ᵒᵖ : hasTerminal (𝒞 ᵒᵖ)
    hasTerminal.⊤ hasTerminal:ᵒᵖ = ⊥
    hasTerminal.isTerminal:⊤ hasTerminal:ᵒᵖ = it
  instance
    hasFiniteProducts:ᵒᵖ : hasFiniteProducts (𝒞 ᵒᵖ)
    hasFiniteProducts.hasTerminal:this hasFiniteProducts:ᵒᵖ = hasTerminal:ᵒᵖ
    hasFiniteProducts.hasProducts:this hasFiniteProducts:ᵒᵖ = hasProducts:ᵒᵖ



