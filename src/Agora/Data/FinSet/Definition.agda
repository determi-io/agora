-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module Agora.Data.FinSet.Definition where

open import Agora.Conventions
open import Agora.Data.Product.Definition
open import Agora.Data.Sum.Definition
open import Agora.Data.Fin.Definition

open import Agora.Data.Universe.Instance.Setoid


record isFinite (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field size : ℕ
  field index : A -> Fin size
  field isIso:index : isIso-𝒰 index

  index⁻¹ : Fin size -> A
  index⁻¹ = inverse-𝒰 {{isIso:index}}

open isFinite using (size) public
open isFinite {{...}} using (index ; isIso:index ; index⁻¹) public



