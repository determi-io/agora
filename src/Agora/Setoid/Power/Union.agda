-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Setoid.Power.Union where

open import Agora.Conventions
open import Agora.Data.Prop.Definition
open import Agora.Data.Product.Definition
open import Agora.Setoid.Definition
open import Agora.Setoid.Instance.Category
open import Agora.Setoid.Power.Definition


----------------------------------------------------------
-- Finitary intersections
----------------------------------------------------------

module _ {A : 𝐒𝐭𝐝 𝑖} where

  module _
         {U : ⟨ A ⟩ -> Prop _} {{_ : isSubsetoid U}}
         {V : ⟨ A ⟩ -> Prop _} {{_ : isSubsetoid V}}
         where
    instance
      isSubsetoid:∪-𝒫-𝐒𝐭𝐝 : isSubsetoid (U ∪ᵘ V)
      isSubsetoid:∪-𝒫-𝐒𝐭𝐝 = record
        { transp-∼ = λ a∼b a∈ -> case a∈ of
                                         (λ a∈U -> left (transp-∼ a∼b a∈U))
                                         λ a∈V -> right (transp-∼ a∼b a∈V)
        }

  _∪-𝒫-𝐒𝐭𝐝_ : 𝒫 A -> 𝒫 A -> 𝒫 A
  _∪-𝒫-𝐒𝐭𝐝_ U V = U ∪ V



  instance
    isSubsetoid:∅-𝒫-𝐒𝐭𝐝 : isSubsetoid {X = ⟨ A ⟩} ∅
    isSubsetoid:∅-𝒫-𝐒𝐭𝐝 = record
      { transp-∼ = λ a∼b ()
      }

  ∅-𝒫-𝐒𝐭𝐝 : 𝒫 A
  ∅-𝒫-𝐒𝐭𝐝 = ∅


----------------------------------------------------------
-- Indexed intersections
----------------------------------------------------------

module _ {A : 𝐒𝐭𝐝 𝑖} {I : 𝒰₀} where
  -- module _ {Uᵢ : I -> ⟨ A ⟩ -> Prop _} {{_ : ∀{i} -> isSubsetoid (Uᵢ i)}} where
  module _ (Uᵢ : I -> 𝒫 A) where
    instance
      isSubsetoid:⋃-𝒫-𝐒𝐭𝐝 : isSubsetoid (⋃ᵘ Uᵢ)
      isSubsetoid:⋃-𝒫-𝐒𝐭𝐝 = record
        { transp-∼ = λ a∼b (i , aᵢ∈U) → i , transp-∼ {{_}} {{of Uᵢ i}} a∼b (aᵢ∈U)
        }

  ⋃-𝒫-𝐒𝐭𝐝 : (Uᵢ : I -> 𝒫 A) -> 𝒫 A
  ⋃-𝒫-𝐒𝐭𝐝 Uᵢ = ⋃ᵘ Uᵢ since isSubsetoid:⋃-𝒫-𝐒𝐭𝐝 Uᵢ



