-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Category.Opposite.Strict.Instance.Monoid where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Algebra.Monoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Opposite.Strict


module _ {𝒞 : Category 𝑖} where
  -- private instance
  --   _ : isSetoid ⟨ 𝒞 ⟩
  --   _ = isSetoid:byCategory

  -- module _ {{Mp : isMonoid (⟨ 𝒞 ⟩ since isSetoid:byCategory)}} where
  --   instance
  --     isMonoid:ᵒᵖ :  isMonoid (⟨ 𝒞 ⟩ since isSetoid:byCategory {{of 𝒞 ᵒᵖ}})
  --     isMonoid._⋆_ isMonoid:ᵒᵖ = _⋆_ {{Mp}}
  --     isMonoid.◌ isMonoid:ᵒᵖ = ◌ {{Mp}}
  --     isMonoid.unit-l-⋆ isMonoid:ᵒᵖ = ⟨ sym-≅ unit-l-⋆ ⟩ since {!!}
  --     isMonoid.unit-r-⋆ isMonoid:ᵒᵖ = {!!}
  --     isMonoid.assoc-l-⋆ isMonoid:ᵒᵖ = {!!}
  --     isMonoid._≀⋆≀_ isMonoid:ᵒᵖ = {!!}

  ≅ᵒᵖ⁻¹ : ∀{a b : ⟨ 𝒞 ⟩} -> (_≅_ {{of 𝒞 ᵒᵖ}} a b) -> (a ≅ b)
  ≅ᵒᵖ⁻¹ f = inverse-◆ {{of 𝒞 ᵒᵖ}} (of f) since
            record
            { inverse-◆ = ⟨ f ⟩
            ; inv-r-◆   = inv-r-◆ {{of 𝒞 ᵒᵖ}} (of f)
            ; inv-l-◆   = inv-l-◆ {{of 𝒞 ᵒᵖ}} (of f)
            }


  module _ {{Mp : isMonoid (⟨ 𝒞 ⟩ since isSetoid:byCategory {{of 𝒞 ᵒᵖ}})}} where
    isMonoid:byᵒᵖ :  isMonoid (⟨ 𝒞 ⟩ since isSetoid:byCategory {{of 𝒞}})
    isMonoid._⋆_ isMonoid:byᵒᵖ        = _⋆_ {{Mp}}
    isMonoid.◌ isMonoid:byᵒᵖ          = ◌ {{Mp}}
    isMonoid.unit-l-⋆ isMonoid:byᵒᵖ   = ≅ᵒᵖ⁻¹ unit-l-⋆
    isMonoid.unit-r-⋆ isMonoid:byᵒᵖ   = ≅ᵒᵖ⁻¹ unit-r-⋆
    isMonoid.assoc-l-⋆ isMonoid:byᵒᵖ  = ≅ᵒᵖ⁻¹ assoc-l-⋆
    isMonoid._≀⋆≀_ isMonoid:byᵒᵖ = {!!}





