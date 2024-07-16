-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Groupoid.Definition where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso

record isGroupoid (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field isIso:hom : ∀{a b : ⟨ 𝒞 ⟩} -> (ϕ : a ⟶ b) -> isIso (hom ϕ)

open isGroupoid {{...}} public

module _ {𝒞 : Category 𝑖} {{X : isGroupoid 𝒞}} where
  _⁻¹-𝐆𝐫𝐩𝐝 : ∀{a b : ⟨ 𝒞 ⟩} -> a ⟶ b -> b ⟶ a
  _⁻¹-𝐆𝐫𝐩𝐝 ϕ = (inverse-◆ (isIso:hom ϕ) )

module _ 𝑖 where
  Groupoid = Category 𝑖 :& isGroupoid



