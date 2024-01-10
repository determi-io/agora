
module Agora.Data.Power.Definition where

open import Agora.Conventions

𝒫 : 𝒰 𝑖 -> 𝒰 (𝑖 ⁺)
𝒫 X = X -> 𝒰 _

singl : {X : 𝒰 𝑖} -> X -> 𝒫 X
singl x = λ y -> x ≡-Str y

_∩-𝒫_ : ∀{X : 𝒰 𝑖} -> 𝒫 X -> 𝒫 X -> 𝒫 X
_∩-𝒫_ A B x = A x ×-𝒰 B x

_∪-𝒫_ : ∀{X : 𝒰 𝑖} -> 𝒫 X -> 𝒫 X -> 𝒫 X
_∪-𝒫_ A B x = A x +-𝒰 B x

_≤-𝒫_ : ∀{X : 𝒰 𝑖} -> 𝒫 X -> 𝒫 X -> 𝒰 _
_≤-𝒫_ A B = ∀ x -> A x -> B x



