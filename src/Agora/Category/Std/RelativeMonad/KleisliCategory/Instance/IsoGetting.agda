-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.RelativeMonad.KleisliCategory.Instance.IsoGetting where

open import Agora.Conventions hiding (_⊔_)

open import Agora.Setoid
open import Agora.Setoid.Morphism
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.RelativeMonad.Definition
open import Agora.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition
open import Agora.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Functor.Faithful
open import Agora.Category.Std.Functor.Full
open import Agora.Category.Std.Functor.EssentiallySurjective

record hasIsoGetting (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field getIso : ∀(a b : ⟨ 𝒞 ⟩) -> Maybe (a ≅ b)

open hasIsoGetting {{...}} public


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {F : Functor 𝒞 𝒟} {{_ : isFull F}} {{_ : isFaithful F}}  {{_ : isEssentiallySurjective F}} where

  hasIsoGetting:byFFEso : hasIsoGetting 𝒟 -> hasIsoGetting 𝒞
  hasIsoGetting:byFFEso P = record { getIso = lem-1 }
    where
      instance _ = P

      lem-1 : (a b : ⟨ 𝒞 ⟩) → Maybe (a ≅ b)
      lem-1 a b with getIso (⟨ F ⟩ a) (⟨ F ⟩ b)
      ... | left x = nothing
      ... | just ϕ = right (ψ since Q)
        where
          -- a' = eso (⟨ F ⟩ a)
          -- b' = eso (⟨ F ⟩ b)
          ψ : a ⟶ b
          ψ = surj ⟨ ϕ ⟩

          ψ⁻¹ : b ⟶ a
          ψ⁻¹ = surj (inverse-◆ (of ϕ))

          Q = record { inverse-◆ = ψ⁻¹ ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} }




module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} {𝒟 : Category 𝑗} where
  module _ {J : Functor 𝒞 𝒟} {T : RelativeMonad J}  where

    hasIsoGetting:RelativeKleisli : {{_ : hasIsoGetting 𝒞}} -> hasIsoGetting (𝐑𝐞𝐊𝐥𝐬 T)
    hasIsoGetting:RelativeKleisli = record { getIso = lem-1 }
      where
        lem-1 : (a b : RelativeKleisli T) → Maybe (a ≅ b)
        lem-1 a b with getIso ⟨ a ⟩ ⟨ b ⟩
        ... | nothing = nothing
        ... | just ϕ = right (ψ since P)
          where
            ψ : a ⟶ b
            ψ = incl (map ⟨ ϕ ⟩ ◆ repure)

            ψ⁻¹ : b ⟶ a
            ψ⁻¹ = incl (map (inverse-◆ (of ϕ)) ◆ repure)

            P = record { inverse-◆ = ψ⁻¹ ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} }






