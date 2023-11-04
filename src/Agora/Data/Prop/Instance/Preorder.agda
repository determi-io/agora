
module Agora.Data.Prop.Instance.Preorder where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Order.Preorder
open import Agora.Data.Prop.Definition
open import Agora.Data.Prop.Instance.Setoid
open import Agora.Data.Universe.Definition

instance
  isPreorder:Prop : isPreorder _ ′ Prop 𝑖 ′
  isPreorder._≤_      isPreorder:Prop = ≤-Base (λ A B -> ⟨ A ⟩ -> ⟨ B ⟩)
  isPreorder.reflexive isPreorder:Prop = incl id-𝒰
  isPreorder._⟡_       isPreorder:Prop f g = incl $ ⟨ f ⟩ ◆-𝒰 ⟨ g ⟩
  isPreorder.transp-≤  isPreorder:Prop ((_ , p)) ((v , _)) f = incl (p ◆-𝒰 ⟨ f ⟩ ◆-𝒰 v)


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
