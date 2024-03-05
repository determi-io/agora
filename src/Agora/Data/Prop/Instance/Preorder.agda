-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Data.Prop.Instance.Preorder where

{-

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Order.Preorder
open import Agora.Data.Prop.Definition
open import Agora.Data.Prop.Instance.Setoid
open import Agora.Data.Universe.Definition

record _≤-Prop_ (A : Prop 𝑖) (B : Prop 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor incl
  field ⟨_⟩ : ⟨ A ⟩ -> ⟨ B ⟩

open _≤-Prop_ public

instance
  isPreorderData:≤-Prop : isPreorderData ′ Prop 𝑖 ′ _≤-Prop_
  isPreorderData:≤-Prop = record
    { reflexive = incl id-𝒰
    ; _⟡_ = λ f g -> incl $ ⟨ f ⟩ ◆-𝒰 ⟨ g ⟩
    ; transp-≤ = λ (_ , p) (v , _) f → incl (p ◆-𝒰 ⟨ f ⟩ ◆-𝒰 v)
    }

instance
  isPreorder:Prop : isPreorder _ ′ Prop 𝑖 ′
  isPreorder:Prop = isPreorder:byDef _≤-Prop_

instance
  isPartialorder:Prop : isPartialorder ′ Prop 𝑖 ′
  isPartialorder.antisym isPartialorder:Prop (incl p) (incl q) = (p , q)


-- instance
--   isPreorder:Prop : isPreorder _ ′ Prop 𝑖 ′
--   isPreorder._≤'_      isPreorder:Prop A B = ⟨ A ⟩ -> ⟨ B ⟩
--   isPreorder.reflexive isPreorder:Prop = incl id-𝒰
--   isPreorder._⟡_       isPreorder:Prop f g = incl $ ⟨ f ⟩ ◆-𝒰 ⟨ g ⟩
--   isPreorder.transp-≤  isPreorder:Prop ((_ , p)) ((v , _)) f = incl (p ◆-𝒰 ⟨ f ⟩ ◆-𝒰 v)


-- instance
--   isPartialorder:Prop : isPartialorder ′ Prop 𝑖 ′
--   isPartialorder.antisym isPartialorder:Prop (incl p) (incl q) = (p , q)

-}
