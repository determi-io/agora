-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Fibration.BaseChange.Definition where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Set.Set.Definition
open import Agora.Set.Set.Instance.Category
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Category.Opposite
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Data.Universe.Definition
open import Agora.Data.Universe.Instance.Category


record hasBaseChange 𝑗 (𝒞 : Category 𝑖) : 𝒰 (𝑗 ⁺ ､ 𝑖) where
  constructor basechange
  field Change : Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)

  _*! : ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> Functor (⟨ Change ⟩ b) (⟨ Change ⟩ a)
  _*! f = map {{of Change}} (f)

  field ∃! : ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> Functor (⟨ Change ⟩ a) (⟨ Change ⟩ b)
  field ∀! : ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> Functor (⟨ Change ⟩ a) (⟨ Change ⟩ b)

open hasBaseChange {{...}} public
  -- ∃!  ∀! *!







{-
record hasBaseChange (𝒞 : Category 𝑖) : 𝒰 (𝑖 ⁺) where
  constructor basechange
  field MyTarget : 𝒰₀
  field myMap : ∀{a b : ⟨ 𝒞 ⟩} -> (a ⟶ b) -> MyTarget -> MyTarget

open hasBaseChange {{...}} public

instance
  hasBaseChange:Set1 : hasBaseChange (𝐓𝐲𝐩𝐞 𝑖)
  hasBaseChange:Set1 = basechange ℕ (const (const 1))

instance
  hasBaseChange:Set2 : hasBaseChange (𝐓𝐲𝐩𝐞 𝑖)
  hasBaseChange:Set2 = basechange Bool (const (const false))


mycall : Bool
mycall = myMap {a = ℕ} {b = ℕ} (id) true

-}
