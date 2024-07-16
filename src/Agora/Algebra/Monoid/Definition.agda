-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Algebra.Monoid.Definition where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Data.Universe.Definition
open import Agora.Data.Product.Definition



record isMonoid (A : Set) : Set where
  field unit : A
  field _⋆_ : A -> A -> A

open isMonoid {{...}} public


Monoid : _
Monoid = Set :& isMonoid

record isCommutative (M : Monoid) : Set where


CommutativeMonoid = Monoid :& isCommutative


module _ {A : CommutativeMonoid} where
  test2 : ⟨ A ⟩ -> ⟨ A ⟩
  test2 a = a ⋆ {!!}



