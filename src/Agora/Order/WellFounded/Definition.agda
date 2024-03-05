-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Order.WellFounded.Definition where

{-
open import Agora.Set.Induction.WellFounded
open import Agora.Conventions


record isWF 𝑗 (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺)) where
  field _≪_ : A -> A -> 𝒰 𝑗
  field wellFounded : WellFounded _≪_
open isWF {{...}} public

WF : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
WF 𝑖 = (𝒰 (𝑖 ⌄ 0)) :& isWF (𝑖 ⌄ 1)

module _ {A : 𝒰 𝑖} {{_ : isWF 𝑗 A}} where
  _⪣_ : A -> A -> 𝒰 _
  _⪣_ a b = (a ≡-Str b) +-𝒰 (a ≪ b)

record isWFT (A : WF 𝑖) : 𝒰 (𝑖) where
  field _⟡-≪_ : ∀{a b c : ⟨ A ⟩} -> a ≪ b -> b ≪ c -> a ≪ c

open isWFT {{...}} public

WFT : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
WFT 𝑖 = (WF 𝑖) :& isWFT

record isWFT0 (A : WFT 𝑖) : 𝒰 𝑖 where
  field ⊥-WFT : ⟨ A ⟩
  field initial-⊥-WFT : ∀{a} -> ⊥-WFT ⪣ a

open isWFT0 {{...}} public

WFT0 : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
WFT0 𝑖 = (WFT 𝑖) :& isWFT0


-}
