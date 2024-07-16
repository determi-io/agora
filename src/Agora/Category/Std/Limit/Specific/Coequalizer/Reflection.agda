-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Limit.Specific.Coequalizer.Reflection where

open import Agora.Conventions hiding (_⊔_)

open import Agora.Setoid
open import Agora.Set.Discrete
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Morphism.Iso

-- open import Agora.Category.Std.Category.Subcategory.Full
open import Agora.Category.Std.Limit.Specific.Coequalizer.Definition

open import Agora.Category.Std.Functor.Faithful
open import Agora.Category.Std.Functor.Full
open import Agora.Category.Std.Functor.EssentiallySurjective
open import Agora.Setoid.Morphism


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {F : Functor 𝒞 𝒟} {{_ : isFull F}} {{_ : isFaithful F}} where

  module _ {a b x : ⟨ 𝒞 ⟩} {f g : a ⟶ b} (P : isCoequalizer (map f) (map g) (⟨ F ⟩ x)) where
    private
      instance _ = P
      π₌' : b ⟶ x
      π₌' = surj π₌

    isCoequalizer:byFullyFaithfull : isCoequalizer f g x
    isCoequalizer.π₌ isCoequalizer:byFullyFaithfull = π₌'
    isCoequalizer.equate-π₌ isCoequalizer:byFullyFaithfull = {!!}
    isCoequalizer.compute-Coeq isCoequalizer:byFullyFaithfull = {!!}
    isCoequalizer.isEpi:π₌ isCoequalizer:byFullyFaithfull = {!!}

