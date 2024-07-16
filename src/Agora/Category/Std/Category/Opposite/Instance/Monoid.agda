-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Category.Opposite.Instance.Monoid where

open import Agora.Conventions

open import Agora.Setoid
open import Agora.Algebra.Monoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Opposite.Definition
open import Agora.Category.Std.Morphism.Iso


module _ {𝒞 : Category 𝑖} where
  private instance
    _ : isSetoid ⟨ 𝒞 ⟩
    _ = isSetoid:byCategory

    _ : isSetoid (𝒞 ᵒᵖ⌯)
    _ = isSetoid:byCategory

  module _ {{_ : isMonoid ′ ⟨ 𝒞 ⟩ ′}} where

    instance
      isMonoid:ᵒᵖ : isMonoid (𝒞 ᵒᵖ⌯)
      isMonoid:ᵒᵖ = record
                      { _⋆_ = λ a b -> incl (⟨ a ⟩ ⋆ ⟨ b ⟩)
                      ; ◌ = incl ◌
                      ; unit-l-⋆ = {!!}
                      ; unit-r-⋆ = {!!}
                      ; assoc-l-⋆ = {!!}
                      ; _≀⋆≀_ = {!!}
                      }



