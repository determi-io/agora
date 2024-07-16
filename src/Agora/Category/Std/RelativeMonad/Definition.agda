-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.RelativeMonad.Definition where

open import Agora.Conventions

open import Agora.Setoid
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Category.Instance.Category


-- | Let [..], [..].
module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  -- [Definition]
  -- | Let [..] be a functor.
  module _ (J : Functor 𝒞 𝒟) where
    -- |> We say that [..], if the following data is given:
    record isRelativeMonad  (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
      constructor relativemonad
      field repure : ∀{a : ⟨ 𝒞 ⟩} -> ⟨ J ⟩ a ⟶ ⟨ F ⟩ a
      field reext : ∀{a b : ⟨ 𝒞 ⟩} -> (f : ⟨ J ⟩ a ⟶ ⟨ F ⟩ b) -> ⟨ F ⟩ a ⟶ ⟨ F ⟩ b
      field reunit-l : ∀{a b : ⟨ 𝒞 ⟩} -> {f : ⟨ J ⟩ a ⟶ ⟨ F ⟩ b} -> repure ◆ reext f ∼ f
      field reunit-r : ∀{a : ⟨ 𝒞 ⟩} -> reext (repure {a = a}) ∼ id
      field reassoc : ∀{a b c : ⟨ 𝒞 ⟩} -> {f : ⟨ J ⟩ a ⟶ ⟨ F ⟩ b} {g : ⟨ J ⟩ b ⟶ ⟨ F ⟩ c} -> reext f ◆ reext g ∼ reext (f ◆ reext g)


    open isRelativeMonad {{...}} public
    -- //

  -- [Hide]
  module _ (J : Functor 𝒞 𝒟) where
    RelativeMonad = _ :& isRelativeMonad J
  -- //






