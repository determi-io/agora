
module Agora.Data.Prop.Instance.HeytingAlgebra where

{-

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Order.HeytingAlgebra
open import Agora.Data.Prop.Definition
open import Agora.Data.Prop.Instance.Setoid
open import Agora.Data.Prop.Instance.Preorder
open import Agora.Data.Prop.Instance.Lattice
open import Agora.Data.Universe.Definition
open import Agora.Data.Universe.Instance.Preorder
open import Agora.Data.Universe.Instance.Lattice
open import Agora.Data.Sum.Definition

instance
  isHeytingAlgebra:Prop : isHeytingAlgebra ′ Prop 𝑖 ′
  isHeytingAlgebra._⇒_     isHeytingAlgebra:Prop A B = ∣ (⟨ A ⟩ -> ⟨ B ⟩) ∣
  isHeytingAlgebra.embed-⇒ isHeytingAlgebra:Prop = incl (λ a b -> a , b)
  isHeytingAlgebra.eval-⇒  isHeytingAlgebra:Prop = incl (λ (a , f) -> f a)

-}
