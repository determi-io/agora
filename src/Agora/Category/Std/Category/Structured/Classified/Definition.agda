


module Agora.Category.Std.Category.Structured.Classified.Definition where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice


record isClassified (X : JoinSemilattice 𝑗) (𝒞 : Category 𝑖) : 𝒰 (𝑗 ､ 𝑖) where
  field class : ∀{a b : ⟨ 𝒞 ⟩} -> a ⟶ b -> ⟨ X ⟩
  field preserve-◆ : ∀{a b c : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> (g : b ⟶ c)
                     -> class (f ◆ g) ∼ (class f ∨ class g)
  field preserve-id : ∀{a : ⟨ 𝒞 ⟩} -> class (id {a = a}) ∼ ⊥

open isClassified {{...}} public



