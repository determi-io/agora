-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Limit.Specific.Coproduct.Preservation.Definition where

open import Agora.Conventions hiding (_⊔_)
open import Agora.Setoid
-- open import Agora.Data.Fin.Definition
open import Agora.Data.Product.Definition
open import Agora.Data.Sum.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Notation.Associativity

open import Agora.Category.Std.Limit.Specific.Coproduct.Definition


-- module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} {𝒟 : 𝒰 𝑘} {{_ : isCategory {𝑖} 𝒟}} where


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record preservesCoproduct (F : Functor 𝒞 𝒟) (a b x : ⟨ 𝒞 ⟩) {{_ : isCoproduct a b x}} : 𝒰 (𝑖 ､ 𝑗) where
    field {{preserve-isCoproduct}} : isCoproduct (⟨ F ⟩ a) (⟨ F ⟩ b) (⟨ F ⟩ x)
    field preserve-ι₀ : map {{of F}} ι₀ ∼ ι₀
    field preserve-ι₁ : map {{of F}} ι₁ ∼ ι₁

  open preservesCoproduct {{...}} public

  record preservesInitial (F : Functor 𝒞 𝒟) (a : ⟨ 𝒞 ⟩) {{_ : isInitial a}} : 𝒰 (𝑖 ､ 𝑗) where
    field {{preserve-Initial}} : isInitial (⟨ F ⟩ a)

  open preservesInitial {{...}} public

  module _ {{_ : hasFiniteCoproducts 𝒞}} where
    record isFiniteCoproductPreserving (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
      field {{preservesCoproducts:this}} : ∀{a b : ⟨ 𝒞 ⟩} -> preservesCoproduct F a b (a ⊔ b)
      field {{preservesInitial:this}} : preservesInitial F ⊥

    open isFiniteCoproductPreserving {{...}} public


    module _ {F : Functor 𝒞 𝒟} {{_ : isFiniteCoproductPreserving F}} {{_ : hasFiniteCoproducts 𝒟}} where
      preserves-⊔ : ∀{a b : ⟨ 𝒞 ⟩} -> ⟨ F ⟩ (a ⊔ b) ≅ ⟨ F ⟩ a ⊔ ⟨ F ⟩ b
      preserves-⊔ {a} {b} = ≅:byIsCoproduct
        where
          instance
            _ : isCoproduct (⟨ F ⟩ a) (⟨ F ⟩ b) (⟨ F ⟩ (a ⊔ b))
            _ = preserve-isCoproduct

      preserves-⊥ : ⟨ F ⟩ ⊥ ≅ ⊥
      preserves-⊥ = ≅:byIsInitial





