-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Universe.Definition where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Limit.Specific.Pullback

module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory {𝑖} 𝒞}} where
  _⟶[_]_ : (a : 𝒞) -> ({a b : 𝒞} -> a ⟶ b -> 𝒰 𝑘) -> (b : 𝒞) -> 𝒰 _
  _⟶[_]_ a S b = ∑ λ (f : a ⟶ b) -> S f

module _ (𝒞 : Category 𝑖) where
  record isUniverse (S : {a b : ⟨ 𝒞 ⟩} -> a ⟶ b -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
    field hasPullback:isUniverse : ∀{a b x : ⟨ 𝒞 ⟩}
            -> (f : a ⟶[ S ] x)
            -> (g : b ⟶ x)
            -> hasPullback 𝒞 (fst f , g)

    -- _◰-Universe_ : ∀{a b x : ⟨ 𝒞 ⟩}
    --         -> (f : a ⟶[ S ] x)
    --         -> (g : b ⟶ x)
    --         -> PullbackCandidate (f , g)
    -- _◰-Universe_ f g = ?

    field pullbackStable : ∀{a b x : ⟨ 𝒞 ⟩}
            -> (f : a ⟶[ S ] x)
            -> (g : b ⟶ x)
            -> S (pb₀ (↳ hasPullback:isUniverse f g))

  Universe : ∀ 𝑗 -> _
  Universe 𝑗 = _ :& isUniverse {𝑗 = 𝑗}

open import Agora.Category.Std.Limit.Specific.Product.Definition
module _ {𝒞 : Category 𝑖} {{_ : hasTerminal 𝒞}} where
  record containsTerminal (𝒮 : Universe 𝒞 𝑗) : 𝒰 𝑖 where











