-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.RelativeMonad.Finitary.Definition where

open import Agora.Conventions

-- open import Agora.Data.List.Variant.Binary.Natural
open import Agora.Setoid
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Category.Instance.Category

open import Agora.Category.Std.RelativeMonad.Definition

open import Agora.Data.Indexed.Definition
open import Agora.Data.FiniteIndexed.Definition
open import Agora.Data.Universe.Definition
open import Agora.Data.Universe.Instance.Category
open import Agora.Category.Std.Category.Subcategory.Full

open import Agora.Data.List.Variant.Binary.Element.As.Indexed


module _ (I : 𝒰 𝑖) where
  private
    fin : 𝐅𝐢𝐧𝐈𝐱 I -> (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖))
    fin = 𝑓𝑢𝑙𝑙 _ 𝑒𝑙
  macro
    𝑓𝑖𝑛 = #structureOn fin

  FinitaryRelativeMonad : 𝒰 _
  FinitaryRelativeMonad = RelativeMonad 𝑓𝑖𝑛





