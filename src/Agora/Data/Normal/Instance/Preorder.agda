-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Data.Normal.Instance.Preorder where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Order.Preorder

open import Agora.Data.Normal.Definition
open import Agora.Data.Normal.Instance.Setoid

module _ { X : Normalizable 𝑖} {{_ : isPreorder 𝑗 ′ ⟨ X ⟩ ′}} where

  record _≤-𝒩_ (a b : 𝒩 X) : 𝒰 𝑗 where
    constructor incl
    field ⟨_⟩ : ⟨ a ⟩ ≤ ⟨ b ⟩

  open _≤-𝒩_ public

  transp-≤-𝒩 : {a₀ a₁ b₀ b₁ : MakeUniverse ⟨ X ⟩ :& isNormalform X} →
      a₀ ∼-Normalform a₁ → b₀ ∼-Normalform b₁ → a₀ ≤-𝒩 b₀ → a₁ ≤-𝒩 b₁
  transp-≤-𝒩 (incl refl-≡) (incl refl-≡) (incl ϕ) = incl ϕ

  instance
    isPreorderData:≤-𝒩 : isPreorderData (𝒩 X) _≤-𝒩_
    isPreorderData:≤-𝒩 = record
      { refl-≤ = incl refl-≤
      ; _⟡_ = λ ϕ ψ -> incl (⟨ ϕ ⟩ ⟡ ⟨ ψ ⟩)
      ; transp-≤ = transp-≤-𝒩
      }

  instance
    isPreorder:𝒩 : isPreorder 𝑗 (𝒩 X)
    isPreorder:𝒩 = record { _≤_ = _≤-𝒩_ }

  module _ {{_ : isDecidablePreorder ′ ⟨ X ⟩ ′}} where

    decide-≤-𝒩 : (a b : Normalform X) → (¬ a ≤ b) +-𝒰 (a ≤ b)
    decide-≤-𝒩 (a since ap) (b since bp) with decide-≤ a b
    ... | no p = no λ P -> p ⟨ P ⟩
    ... | yes p = yes (incl p)

    instance
      isDecidablePreorder:𝒩 : isDecidablePreorder (𝒩 X)
      isDecidablePreorder:𝒩 = record { decide-≤ = decide-≤-𝒩 }


