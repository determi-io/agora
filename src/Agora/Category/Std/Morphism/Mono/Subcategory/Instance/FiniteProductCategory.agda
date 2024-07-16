-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Morphism.Mono.Subcategory.Instance.FiniteProductCategory where

open import Agora.Conventions hiding (_⊔_)

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Category.Subcategory.Definition
open import Agora.Category.Std.Morphism.Mono.Definition
open import Agora.Category.Std.Morphism.Mono.Subcategory.Definition
open import Agora.Category.Std.Limit.Specific.Product

-- module _ {𝒞 : Category 𝑖} {{_ : hasFiniteProducts 𝒞}} where


--   _⊓-𝐒𝐮𝐛ₘₒₙₒ_ : (a b : 𝐒𝐮𝐛ₘₒₙₒ 𝒞) -> 𝐒𝐮𝐛ₘₒₙₒ 𝒞
--   _⊓-𝐒𝐮𝐛ₘₒₙₒ_ a b = incl (⟨ a ⟩ ⊓ ⟨ b ⟩)

--   module _ {a b : 𝐒𝐮𝐛ₘₒₙₒ 𝒞} where
--     isProduct:⊓-𝐒𝐮𝐛ₘₒₙₒ : isProduct a b (a ⊓-𝐒𝐮𝐛ₘₒₙₒ b)
--     isProduct.π₀ isProduct:⊓-𝐒𝐮𝐛ₘₒₙₒ = {!!}
--     isProduct.π₁ isProduct:⊓-𝐒𝐮𝐛ₘₒₙₒ = {!!}
--     isProduct.⧼ isProduct:⊓-𝐒𝐮𝐛ₘₒₙₒ ⧽ = {!!}
--     isProduct.isSetoidHom:⧼⧽ isProduct:⊓-𝐒𝐮𝐛ₘₒₙₒ = {!!}
--     isProduct.reduce-π₀ isProduct:⊓-𝐒𝐮𝐛ₘₒₙₒ = {!!}
--     isProduct.reduce-π₁ isProduct:⊓-𝐒𝐮𝐛ₘₒₙₒ = {!!}
--     isProduct.expand-⊓ isProduct:⊓-𝐒𝐮𝐛ₘₒₙₒ = {!!}

--   instance
--     hasFiniteProducts:𝐒𝐮𝐛ₘₒₙₒ : hasFiniteProducts (𝐒𝐮𝐛ₘₒₙₒ 𝒞)
--     hasFiniteProducts:𝐒𝐮𝐛ₘₒₙₒ = {!!}


