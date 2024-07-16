-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Setoid.As.Groupoid where

open import Agora.Conventions
-- open import Agora.Data.Prop.Definition
-- open import Agora.Data.Product.Definition
open import Agora.Setoid.Definition
open import Agora.Setoid.Codiscrete
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Groupoid.Definition
open import Agora.Setoid.As.Category
open import Agora.Category.Std.Morphism.Iso

-- NOTE:
-- This concept does not make much sense.
-- A setoid has as much information as a category,
-- but does not follow the laws of categories.
-- Thus it is not possible to embed it in the structure
-- of a category, without building a quotient for
-- the equality of arrows.


{-
module _ {A : 𝒰 𝑖} {{Ap : isSetoid {𝑗} A}} where

  private instance
    _ : isCategory {_ , _} A
    _ = isCategory:bySetoid

  isGroupoid:bySetoid : isGroupoid {_ , _ , _} ′ A ′
  isGroupoid.isIso:hom isGroupoid:bySetoid {a} {b} {ϕ} = P
    where
      P : isIso (hom ϕ)
      P = record
          { inverse-◆ = sym ϕ
          ; inv-r-◆   = {!!}
          ; inv-l-◆   = {!!}
          }
-}

