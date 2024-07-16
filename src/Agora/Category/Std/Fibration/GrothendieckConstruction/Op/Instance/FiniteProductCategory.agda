-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Fibration.GrothendieckConstruction.Op.Instance.FiniteProductCategory where

open import Agora.Conventions hiding (_⊔_)

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Opposite
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition
open import Agora.Category.Std.Limit.Specific.Product

open import Agora.Category.Std.Fibration.GrothendieckConstruction.Op.Definition


module _ {𝒞 : Category 𝑖} {F : Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)}
         {{_ : hasProducts 𝒞}} {{_ : ∀{c : ⟨ 𝒞 ⟩} -> hasProducts (⟨ F ⟩ c)}}
  where

  private
    instance
      isCategory:F : ∀{b : ⟨ 𝒞 ⟩} -> isCategory (⟨ ⟨ F ⟩ b ⟩)
      isCategory:F {b} = of ⟨ F ⟩ b

    instance
      isSetoid:F : ∀{b : ⟨ 𝒞 ⟩} {x y : ⟨ ⟨ F ⟩ b ⟩} -> isSetoid (x ⟶ y)
      isSetoid:F {b} = isSetoid:Hom {{of ⟨ F ⟩ b}}

    instance
      isProduct:F : ∀{c : ⟨ 𝒞 ⟩} -> {a b : ⟨ ⟨ F ⟩ c ⟩} -> isProduct a b (a ⊓ b)
      isProduct:F = isProduct:⊓

  infixl 80 _⊓-⨊ᵒᵖ_

  _⊓-⨊ᵒᵖ_ : ⨊ᵒᵖ F -> ⨊ᵒᵖ F -> ⨊ᵒᵖ F
  _⊓-⨊ᵒᵖ_ a b = (base a ⊓ base b) , ⟨ map π₀ ⟩ (fib a) ⊓ ⟨ map π₁ ⟩ (fib b)

  module _ {a b : ⨊ᵒᵖ F} where
    π₀-⨊ᵒᵖ : a ⊓-⨊ᵒᵖ b ⟶ a
    π₀-⨊ᵒᵖ = π₀ , π₀
