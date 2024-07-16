-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Category.As.Monoid.Special where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Set.Discrete
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Order.WellFounded.Definition
open import Agora.Data.Prop.Everything
open import Agora.Algebra.Monoid.Definition
open import Agora.Algebra.MonoidWithZero.Definition
open import Agora.Algebra.MonoidWithZero.Special
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Sized.Definition
open import Agora.Category.Std.Category.As.Monoid.Definition

module _ {𝒞 : 𝒰 _} {{_ : SizedCategory 𝑖 on 𝒞}} where


  Special-PathMon : Submonoid (𝖯𝖺𝗍𝗁𝖬𝗈𝗇 ′ 𝒞 ′)
  Special-PathMon = ′ S ′
    where
      S : 𝖯𝖺𝗍𝗁𝖬𝗈𝗇 ′ 𝒞 ′ -> Prop _
      S [] = ⊤
      S idp = ⊤
      S (arrow {a} {b} f) = ∣ Lift (sizeO b ≪ sizeO a) ∣

      instance
        isSubsetoid:S : isSubsetoid S
        isSubsetoid:S = {!!}

      instance
        isSubmonoid:S : isSubmonoid ′ S ′
        isSubmonoid:S = {!!}


  instance
    hasSpecial:PathMon : hasSpecial (𝖯𝖺𝗍𝗁𝖬𝗈𝗇 ′ 𝒞 ′)
    hasSpecial:PathMon = record { Special = Special-PathMon }






