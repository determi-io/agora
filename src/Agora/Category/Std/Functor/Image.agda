
module Agora.Category.Std.Functor.Image where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Functor.Definition
open import Agora.Setoid.Morphism


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  module _ (F : Functor 𝒞 𝒟) where

    inEssentialImage : ⟨ 𝒟 ⟩ -> 𝒰 _
    inEssentialImage d = ∑ λ (c : ⟨ 𝒞 ⟩) -> ⟨ F ⟩ c ≅ d

    EssentialImage : 𝒰 _
    EssentialImage = ∑ inEssentialImage


