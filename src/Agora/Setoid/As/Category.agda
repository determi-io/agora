-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Setoid.As.Category where

open import Agora.Conventions
-- open import Agora.Data.Prop.Definition
-- open import Agora.Data.Product.Definition
open import Agora.Setoid.Definition
open import Agora.Setoid.Discrete
open import Agora.Category.Std.Category.Definition

-- NOTE:
-- This concept does not make much sense.
-- A setoid has as much information as a category,
-- but does not follow the laws of categories.
-- Thus it is not possible to embed it in the structure
-- of a category, without building a quotient for
-- the equality of arrows.

{-
module _ {A : 𝒰 𝑖} {{_ : isSetoid {𝑗} A}} where

  isCategory:bySetoid : isCategory {_ , _} A
  isCategory.Hom isCategory:bySetoid          = λ a b -> a ∼ b
  isCategory.isSetoid:Hom isCategory:bySetoid = isSetoid:byDiscrete
  isCategory.id isCategory:bySetoid           = refl
  isCategory._◆_ isCategory:bySetoid          = _∙_
  isCategory.unit-l-◆ isCategory:bySetoid     = {!!}
  isCategory.unit-r-◆ isCategory:bySetoid     = {!!}
  isCategory.unit-2-◆ isCategory:bySetoid     = {!!}
  isCategory.assoc-l-◆ isCategory:bySetoid    = {!!}
  isCategory.assoc-r-◆ isCategory:bySetoid    = {!!}
  isCategory._◈_ isCategory:bySetoid          = λ x x₁ → {!!}



open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Functor.Definition

module _ {A : 𝒰 𝑖} {{_ : isSetoid {𝑗} A}} {ℬ : Category 𝑘} where
  private
    instance
      _ : isSetoid ⟨ ℬ ⟩
      _ = isSetoid:byCategory

  instance
    isFunctor:bySetoid : {f : A -> ⟨ ℬ ⟩} {{_ : isSetoidHom ′ A ′ ′ ⟨ ℬ ⟩ ′ f}} -> isFunctor (A since isCategory:bySetoid) ℬ f
    isFunctor.map (isFunctor:bySetoid {f}) = λ p → ⟨ cong-∼ p ⟩
    isFunctor.isSetoidHom:map (isFunctor:bySetoid {f}) = record { cong-∼ = λ {a} {b} p → transport (λ i -> ⟨ cong-∼ a ⟩ ∼ ⟨ cong-∼ (p i) ⟩) refl }
    isFunctor.functoriality-id (isFunctor:bySetoid {f}) = {!!}
    isFunctor.functoriality-◆ (isFunctor:bySetoid {f}) = {!!}

-}

