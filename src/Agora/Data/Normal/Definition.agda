
module Agora.Data.Normal.Definition where

open import Agora.Conventions
open import Agora.Setoid.Definition

-- We define a datatype for carrying normal forms
-- of normalizable setoids.

record MakeUniverse (X : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : X

open MakeUniverse public

instance
  isUniverseOf:MakeUniverse : ∀{X : 𝒰 𝑖} -> X isUniverseOf[ _ ] (MakeUniverse X)
  isUniverseOf:MakeUniverse = record
                               { Proof = λ a -> isAnything a ℓ₀
                               ; projectUniv = λ a -> ⟨ a ⟩
                               ; projectProof = λ a → record {}
                               ; reconstructObj = λ u x → incl u
                               }

record isNormalizable 𝑘 (X : Setoid 𝑖) : 𝒰 (𝑖 ､ 𝑘 ⁺) where
  field Normal : ⟨ X ⟩ -> 𝒰 𝑘
  field {{isProp:Normal}} : ∀{x} -> isProp (Normal x)
  field normalize : ⟨ X ⟩ -> ⟨ X ⟩
  field normal : ∀{x} -> Normal (normalize x)
  field preserves-∼:normalize : ∀{x} -> normalize x ∼ x
  field cong-∼-normalize : ∀{x y} -> x ∼ y -> normalize x ≡ normalize y

open isNormalizable {{...}} public

Normalizable : ∀ (𝑖 : 𝔏 ^ 3) -> _
Normalizable 𝑖 = Setoid (𝑖 ⌄ 0 ⋯ 1) :& isNormalizable (𝑖 ⌄ 2)

record isNormalform (X : Normalizable 𝑖) (x : MakeUniverse ⟨ X ⟩) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : Normal ⟨ x ⟩

open isNormalform public

Normalform : (X : Normalizable 𝑖) -> _
Normalform X = MakeUniverse ⟨ X ⟩ :& isNormalform X

macro
  𝒩 : (X : Normalizable 𝑖) -> _
  𝒩 X = #structureOn (Normalform X)







