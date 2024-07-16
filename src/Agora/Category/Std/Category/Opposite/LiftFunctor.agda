-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Category.Opposite.LiftFunctor where

open import Agora.Conventions

open import Agora.Setoid
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Category.Opposite.Definition


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  liftFunctor-ᵒᵖ⌯ : (F : Functor 𝒞 𝒟) -> Functor (𝒞 ᵒᵖ⌯) (𝒟 ᵒᵖ⌯)
  liftFunctor-ᵒᵖ⌯ F = G since P
    where
      G : (𝒞 ᵒᵖ⌯) -> (𝒟 ᵒᵖ⌯)
      G (incl a) = incl (⟨ F ⟩ a)

      map-G : ∀{a b : 𝒞 ᵒᵖ⌯} -> (f : a ⟶ b) -> G a ⟶ G b
      map-G (incl f) = incl (map f)

      P : isFunctor _ _ G
      isFunctor.map P = map-G
      isFunctor.isSetoidHom:map P = {!!}
      isFunctor.functoriality-id P = {!!}
      isFunctor.functoriality-◆ P = {!!}



