-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Natural.Definition where

open import Agora.Conventions
open import Agora.Conventions.Prelude.Classes.Structure

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition

--------------------------------------------------------------------------------
-- Natural Transformations



-- [Definition]
-- | Let [..], [..] be again two categories,
module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
-- |> and [..] two parallel functors between them.
  module _ (F G : Functor 𝒞 𝒟) where

-- |> A family of morphisms |α|, where for every |x : 𝒞|, |α ⌄ x : F x ⟶ G x| is an arrow in |𝒟|,
--   is called a *natural transformation* from |F| to |G|,
    record isNatural (α : ∀(x : ⟨ 𝒞 ⟩) -> Hom (⟨ F ⟩ x) (⟨ G ⟩ x)) : 𝒰 (𝑖 ､ 𝑗) where
      constructor natural

-- |> if it is natural, i.e., the following equation holds:
      field naturality : ∀{x y : ⟨ 𝒞 ⟩} -> ∀(f : x ⟶ y) -> α x ◆ mapOf G f ∼ mapOf F f ◆ α y

    open isNatural {{...}} public
--  //

  -- module _ {F G : ⟨ 𝒞 ⟩ -> ⟨ 𝒟 ⟩} where
  --   instance
  --     hasU:Natural : (∀(x : ⟨ 𝒞 ⟩) ->  F x ⟶ G x) isUniverseOf[ _ ] (∀(x : ⟨ 𝒞 ⟩) -> F x ⟶ G x)
  --     hasU:Natural = _isUniverseOf[_]_:byBase

    -- instance
    --   hasU:Natural' : hasU (∀{x : ⟨ 𝒞 ⟩} -> ⟨ F ⟩ x ⟶ ⟨ G ⟩ x) _ _
    --   hasU:Natural' = hasU:Base (∀{x : ⟨ 𝒞 ⟩} -> ⟨ F ⟩ x ⟶ ⟨ G ⟩ x)

  module _ (F G : Functor 𝒞 𝒟) where
    Natural : 𝒰 _
    Natural = (∀ x -> ⟨ F ⟩ x ⟶ ⟨ G ⟩ x) :& isNatural F G

-- unquoteDecl Natural natural = #struct "Nat" (quote isNatural) "α" Natural natural


