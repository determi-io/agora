-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Setoid.Power.Instance.IsDistributive where

open import Agora.Conventions hiding (_⊔_)
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso.Definition
open import Agora.Data.Prop.Definition
open import Agora.Data.Sum.Definition
open import Agora.Setoid.Definition
open import Agora.Setoid.Instance.Category
open import Agora.Setoid.Codiscrete
open import Agora.Setoid.Power.Definition

open import Agora.Setoid.Power.Instance.Category
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition
open import Agora.Category.Std.Limit.Specific.Product.Definition
open import Agora.Setoid.Power.Union
open import Agora.Setoid.Power.Intersection

open import Agora.Setoid.Power.Instance.HasCoproducts
open import Agora.Setoid.Power.Instance.HasProducts


module _ {A : 𝐒𝐭𝐝 𝑖} where
  lem1 : ∀{U V W : 𝒫 A} -> U ⊓ (V ⊔ W) ≅ (U ⊓ V ⊔ U ⊓ W)
  lem1 {U} {V} {W} = f since P
    where
      f : U ⊓ (V ⊔ W) ⟶ (U ⊓ V ⊔ U ⊓ W)
      f = incl (λ (x∈U , x∈V⊔W) → case x∈V⊔W of
                                       (λ x∈V -> left (x∈U , x∈V))
                                       (λ x∈W -> right (x∈U , x∈W)))

      g : (U ⊓ V ⊔ U ⊓ W) ⟶ U ⊓ (V ⊔ W)
      g = incl (λ x → case x of
                           (λ (x∈U , x∈V) -> x∈U , left x∈V)
                           (λ (x∈U , x∈W) -> x∈U , right x∈W)
        )

      P : isIso (hom f)
      P = record
        { inverse-◆ = g
        ; inv-r-◆ = tt
        ; inv-l-◆ = tt
        }

  lem2 : ∀{U V W : 𝒫 A} -> U ⊔ (V ⊓ W) ≅ (U ⊔ V) ⊓ (U ⊔ W)
  lem2 {U} {V} {W} = f since P
    where
      f : U ⊔ (V ⊓ W) ⟶ (U ⊔ V) ⊓ (U ⊔ W)
      f = incl (λ x → case x of
                           (λ x∈U -> left x∈U , left x∈U)
                           (λ (x∈V , x∈W) -> right x∈V , right x∈W))

      g : (U ⊔ V) ⊓ (U ⊔ W) ⟶ U ⊔ (V ⊓ W)
      g = incl (λ (x∈U⊔V , x∈U⊔W) → case x∈U⊔V of
                                         (λ x∈U -> left x∈U)
                                         (λ x∈V -> case x∈U⊔W of
                                                          (λ x∈U -> left x∈U)
                                                          (λ x∈W -> right (x∈V , x∈W))))

      P : isIso (hom f)
      P = record
          { inverse-◆ = g
          ; inv-r-◆ = tt
          ; inv-l-◆ = tt
          }

  module _ {I : 𝒰₀} {U : 𝒫 A} {V : I -> 𝒫 A} where
    lem3 : U ⊓ (⨆ᵢ V) ≅ ⨆[ i ] (U ⊓ V i)
    lem3 = f since P
      where
        f : U ⊓ (⨆ᵢ V) ⟶ ⨆[ i ] (U ⊓ V i)
        ⟨ f ⟩ (x∈U , (i , x∈Vᵢ)) = i , x∈U , x∈Vᵢ

        g : ⨆[ i ] (U ⊓ V i) ⟶ U ⊓ (⨆ᵢ V)
        ⟨ g ⟩ (i , x∈U , x∈Vᵢ) = x∈U , (i , x∈Vᵢ)

        P : isIso (hom f)
        P = record
          { inverse-◆ = g
          ; inv-r-◆ = tt
          ; inv-l-◆ = tt
          }

    --
    -- Constructively we cannot prove the following.
    -- This means that 𝒫 A is completely distributive only in
    -- one direction, not in both.
    --
    -- lem4 : (U ⊔ (⨅ᵢ V) ≅ ⨅[ i ] (U ⊔ V i))
    --


