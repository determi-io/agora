
module Agora.Data.Prop.Instance.Setoid where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Data.Prop.Definition
open import Agora.Data.Universe.Definition

module _ {𝑖} where

  record _∼-Prop_ (A B : Prop 𝑖) : 𝒰 𝑖 where
    constructor _,_
    field ⟨_⟩ : ⟨ A ⟩ -> ⟨ B ⟩
          inv-∼-Prop : Prop.⟨_⟩ B -> Prop.⟨_⟩ A
  open _∼-Prop_ public

  instance
    isEquivRel:∼-Prop : isEquivRel _∼-Prop_
    isEquivRel:∼-Prop = isEquivRel:byDef
      (id-𝒰 , id-𝒰)
      (λ (p , q) -> (q , p))
      (λ (p , q) (v , w) -> (p ◆-𝒰 v , w ◆-𝒰 q))

  instance
    isSetoid:Prop : isSetoid (Prop 𝑖)
    isSetoid:Prop = isSetoid:byDef _∼-Prop_



