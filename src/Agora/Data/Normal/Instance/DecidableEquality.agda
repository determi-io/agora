-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Data.Normal.Instance.DecidableEquality where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Data.Normal.Definition

open Structure

module _ { X : Normalizable 𝑖} {{_ : hasDecidableEquality ⟨ X ⟩}} where

  decide-≡-𝒩 : ∀(a b : 𝒩 X) -> isDecidable (a ≡ b)
  decide-≡-𝒩 (a since ap) (b since bp) with a ≟ b
  ... | no p = no λ {refl-≡ -> p refl-≡}
  ... | yes refl-≡ with force-≡ ⟨ ap ⟩ ⟨ bp ⟩
  ... | refl-≡ = yes refl-≡

  instance
    hasDecidableEquality:𝒩 : hasDecidableEquality (𝒩 X)
    hasDecidableEquality:𝒩 = record { _≟_ = decide-≡-𝒩 }



