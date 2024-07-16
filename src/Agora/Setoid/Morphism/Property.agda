-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Setoid.Morphism.Property where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Category.Std.Morphism.Iso.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Setoid.Morphism.Injective
open import Agora.Data.Universe.Definition
open import Agora.Data.Universe.Instance.Category


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑖} {{_ : isSetoid {𝑖₁} A}} {{_ : isSetoid {𝑖₁} B}} where
  isInjective:byIso : {f : A -> B} {{_ : isSetoidHom ′ A ′ ′ B ′ f}} {{_ : isIso (hom f)}} -> isInjective f
  isInjective:byIso = {!!}


