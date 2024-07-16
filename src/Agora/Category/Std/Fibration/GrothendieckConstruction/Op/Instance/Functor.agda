-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Fibration.GrothendieckConstruction.Op.Instance.Functor where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Opposite
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Fibration.GrothendieckConstruction.Op.Definition



module _ {𝒞 : Category 𝑖} where
  module _ {F G : Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)} where
    mapᵘ-⨊ᵒᵖ : Natural F G -> (⨊ᵒᵖ F) -> (⨊ᵒᵖ G)
    mapᵘ-⨊ᵒᵖ α (a , a⃩) = a , ⟨ ⟨ α ⟩ ⟩ a⃩


    -- module _ (α : Natural F G) where
    --   macro map-⨊ᵒᵖ = #structureOn (mapᵘ-⨊ᵒᵖ α)

    module _ {α : Natural F G} where
      map-map-⨊ᵒᵖ : {a b : ⨊ᵒᵖ F} -> a ⟶ b -> mapᵘ-⨊ᵒᵖ α a ⟶ mapᵘ-⨊ᵒᵖ α b
      map-map-⨊ᵒᵖ (f , f⃩) = f , {!!}

      instance
        isFunctor:mapᵘ-⨊ᵒᵖ : isFunctor (⨊ᵒᵖ F) (⨊ᵒᵖ G) (mapᵘ-⨊ᵒᵖ α)
        isFunctor.map isFunctor:mapᵘ-⨊ᵒᵖ = map-map-⨊ᵒᵖ
        isFunctor.isSetoidHom:map isFunctor:mapᵘ-⨊ᵒᵖ = {!!}
        isFunctor.functoriality-id isFunctor:mapᵘ-⨊ᵒᵖ = {!!}
        isFunctor.functoriality-◆ isFunctor:mapᵘ-⨊ᵒᵖ = {!!}

    module _ (α : Natural F G) where
      macro map-⨊ᵒᵖ = #structureOn (mapᵘ-⨊ᵒᵖ α)

    module _ (α : Natural F G) where
      map-⨊ᵒᵖ' : Functor (⨊ᵒᵖ F) (⨊ᵒᵖ G)
      map-⨊ᵒᵖ' = mapᵘ-⨊ᵒᵖ α since isFunctor:mapᵘ-⨊ᵒᵖ {α = α}


