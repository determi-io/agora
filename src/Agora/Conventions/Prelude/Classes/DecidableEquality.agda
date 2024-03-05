-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Conventions.Prelude.Classes.DecidableEquality where

open import Agora.Conventions.Proprelude
-- open import Agora.Conventions.Prelude.Classes.Operators.Unary
-- open import Agora.Conventions.Prelude.Classes.Cast
-- open import Agora.Conventions.Prelude.Classes.Anything
open import Agora.Conventions.Prelude.Data.StrictId


record hasDecidableEquality {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : ∀ (x y : A) → isDecidable (x ≡ y)

open hasDecidableEquality {{...}} public



