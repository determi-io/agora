-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Category.Structured.FiniteCoproduct.As.Monoid where

open import Agora.Conventions hiding (_⊔_)
open import Agora.Setoid
open import Agora.Algebra.Monoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Opposite
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition
open import Agora.Category.Std.Limit.Specific.Product
open import Agora.Category.Std.Category.Structured.FiniteCoproduct.Definition
open import Agora.Category.Std.Category.Structured.FiniteProduct.Definition
open import Agora.Category.Std.Category.Structured.FiniteProduct.As.Monoid
open import Agora.Category.Std.Category.Structured.FiniteCoproduct.As.FiniteProduct



module _ {𝒞 : 𝒰 _} {{_ : 𝒞 is FiniteCoproductCategory 𝑖}} where

  private instance
    _ : isSetoid 𝒞
    _ = isSetoid:byCategory


  private
    𝒞ᵒᵖ : Category _
    𝒞ᵒᵖ = ′ 𝒞 ′ ᵒᵖ
    instance
      _ : isMonoid (𝒞 since isSetoid:byCategory {{of 𝒞ᵒᵖ}})
      _ = isMonoid:byHasFiniteProducts

  isMonoid:byHasFiniteCoproducts : isMonoid ′ 𝒞 ′
  isMonoid:byHasFiniteCoproducts = isMonoid:byᵒᵖ


module _ {𝒞 : 𝒰 _} {{P : 𝒞 is FiniteCoproductCategory 𝑖}} where
  private instance
    _ : isSetoid 𝒞
    _ = isSetoid:byCategory

    _ : isMonoid ′ 𝒞 ′
    _ = isMonoid:byHasFiniteCoproducts {{P}}

  unit-l-⊔ : ∀{a : 𝒞} -> ⊥ ⊔ a ∼ a
  unit-l-⊔ = unit-l-⋆

  unit-r-⊔ : ∀{a : 𝒞} -> a ⊔ ⊥ ∼ a
  unit-r-⊔ = unit-r-⋆

  assoc-l-⊔ : ∀{a b c : 𝒞} -> (a ⊔ b) ⊔ c ∼ a ⊔ (b ⊔ c)
  assoc-l-⊔ = assoc-l-⋆





