
module Agora.Data.Normal.Instance.Lattice where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import Agora.Data.Normal.Definition
open import Agora.Data.Normal.Instance.Setoid
open import Agora.Data.Normal.Instance.Preorder


module _ { X : Normalizable 𝑖} {{_ : isPreorder 𝑗 ′ ⟨ X ⟩ ′}} {{_ : hasFiniteMeets ′ ⟨ X ⟩ ′}} where

  _∧-𝒩_ : (a b : 𝒩 X) -> 𝒩 X
  _∧-𝒩_ a b = normalize (⟨ a ⟩ ∧ ⟨ b ⟩) since incl normal

  instance
    hasFiniteMeets:𝒩 : hasFiniteMeets (𝒩 X)
    hasFiniteMeets:𝒩 = record
      { ⊤ = normalize ⊤ since incl normal
      ; terminal-⊤ = incl (transp-terminal-⊤ preserves-∼:normalize)
      ; _∧_ = _∧-𝒩_
      ; π₀-∧ = incl (transp-π₀-∧ preserves-∼:normalize)
      ; π₁-∧ = incl (transp-π₁-∧ preserves-∼:normalize)
      ; ⟨_,_⟩-∧ = λ ϕ ψ -> incl (transp-⟨⟩-∧ preserves-∼:normalize ⟨ ϕ ⟩ ⟨ ψ ⟩)
      }


module _ { X : Normalizable 𝑖} {{_ : isPreorder 𝑗 ′ ⟨ X ⟩ ′}} {{_ : hasFiniteJoins ′ ⟨ X ⟩ ′}} where

  _∨-𝒩_ : (a b : 𝒩 X) -> 𝒩 X
  _∨-𝒩_ a b = normalize (⟨ a ⟩ ∨ ⟨ b ⟩) since incl normal

  instance
    hasFiniteJoins:𝒩 : hasFiniteJoins (𝒩 X)
    hasFiniteJoins:𝒩 = record
      { ⊥ = normalize ⊥ since incl normal
      ; initial-⊥ = incl (transp-initial-⊥ preserves-∼:normalize)
      ; _∨_ = _∨-𝒩_
      ; ι₀-∨ = incl (transp-ι₀-∨ preserves-∼:normalize)
      ; ι₁-∨ = incl (transp-ι₁-∨ preserves-∼:normalize)
      ; [_,_]-∨ = λ ϕ ψ -> incl (transp-[]-∨ preserves-∼:normalize ⟨ ϕ ⟩ ⟨ ψ ⟩)
      }

