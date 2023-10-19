

module Agora.Conventions.Prelude.Classes.Discrete where

open import Agora.Conventions.Proprelude
open import Agora.Conventions.Prelude.Data.StrictId

isDecidable : ∀(A : 𝒰 𝑖) -> 𝒰 _
isDecidable A = (¬ A) +-𝒰 A

record isDiscrete (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field _≟-Str_ : (a b : A) -> isDecidable (a ≡-Str b)
open isDiscrete {{...}} public

Discrete : 𝒰 𝑖 -> 𝒰 _
Discrete A = ∀(a b : A) -> isDecidable (a ≡-Str b)


