-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Functor.EssentiallySurjective where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Functor.Definition
open import Agora.Setoid.Morphism
open import Agora.Category.Std.Functor.Image

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  -- instance
  --   _ : isSetoid ⟨ 𝒞 ⟩
  --   _ = isSetoid:byCategory

  --   _ : isSetoid ⟨ 𝒟 ⟩
  --   _ = isSetoid:byCategory

  -- module _ (F : Functor 𝒞 𝒟) where
  --   private
  --     instance
  --       _ : isSetoidHom _ _ ⟨ F ⟩
  --       _ = isSetoidHom:byFunctor

  --   record isEssentiallySurjective : 𝒰 (𝑖 ､ 𝑗) where
  --     field {{isSurjective:this}} : isSurjective ⟨ F ⟩

  --   open isEssentiallySurjective {{...}} public

  record isEssentiallySurjective (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    constructor essentiallysurjective
    field eso : ⟨ 𝒟 ⟩ -> ⟨ 𝒞 ⟩
    field inv-eso : ∀{d : ⟨ 𝒟 ⟩} -> ⟨ F ⟩ (eso d) ≅ d

  open isEssentiallySurjective {{...}} public






