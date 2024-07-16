-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Limit.Specific.Coproduct.Properties.EpiMono where

open import Agora.Conventions hiding (_⊔_)
open import Agora.Setoid
-- open import Agora.Data.Fin.Definition
open import Agora.Data.Product.Definition
open import Agora.Data.Sum.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Morphism.Mono.Definition
open import Agora.Category.Std.Category.Notation.Associativity

open import Agora.Category.Std.Limit.Specific.Coproduct.Definition


module _ {𝒞 : Category 𝑖} where
  module _ {a b x : ⟨ 𝒞 ⟩} {{_ : isCoproduct a b x}} where

    mono-ι₀ : isMono ι₀
    mono-ι₀ = {!!}


