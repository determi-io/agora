-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Conventions.Prelude.Data.Maybe where

open import Agora.Conventions.Proprelude

Maybe : 𝒰 𝑖 -> 𝒰 𝑖
Maybe {𝑖} A = ⊤-𝒰 {𝑖} +-𝒰 A

pattern just a = right a
pattern nothing = left tt

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-Maybe : (f : A -> B) -> Maybe A -> Maybe B
  map-Maybe f (left tt) = left tt
  map-Maybe f (just x) = just (f x)

  bind-Maybe : Maybe A -> (f : A -> Maybe B) -> Maybe B
  bind-Maybe (left tt) f = left tt
  bind-Maybe (just x) f = f x

