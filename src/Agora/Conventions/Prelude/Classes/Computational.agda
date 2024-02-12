

module Agora.Conventions.Prelude.Classes.Computational where

open import Agora.Conventions.Proprelude
open import Agora.Conventions.Prelude.Data.Bool

record IShow (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field show : A -> Text
open IShow {{...}} public

record IBootMonoid (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field mempty : A
        _<>_ : A -> A -> A
  infixl 30 _<>_
open IBootMonoid {{...}} public

record IBootEq (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field _==_ : A -> A -> Bool
open IBootEq {{...}} public

