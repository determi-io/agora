-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Data.Normal.Instance.Setoid where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Data.Normal.Definition

module _ { X : Normalizable 𝑖} where
  record _∼-Normalform_ (x y : 𝒩 X) : 𝒰 (𝑖 ⌄ 0) where
    constructor incl
    field ⟨_⟩ : ⟨ x ⟩ ≡ ⟨ y ⟩

  open _∼-Normalform_ public

  instance
    isEquivRel:∼-Normalform : isEquivRel _∼-Normalform_
    isEquivRel:∼-Normalform = record
      { refl-∼ = incl refl-≡
      ; sym = λ p -> incl (sym-≡ ⟨ p ⟩)
      ; _∙_ = λ p q -> incl (⟨ p ⟩ ∙-≡ ⟨ q ⟩)
      }

  instance
    isSetoid:𝒩 : isSetoid (𝒩 X)
    isSetoid:𝒩 = record { _∼_ = _∼-Normalform_ }


