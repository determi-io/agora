-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Functor.Full where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Setoid.Morphism



module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isFull (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field {{isSurjective:map}} : ∀{a b : ⟨ 𝒞 ⟩} -> isSurjective (map {{of F}} {a} {b})

  open isFull {{...}} public






