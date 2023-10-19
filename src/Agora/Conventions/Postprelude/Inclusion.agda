
module Agora.Conventions.Postprelude.Inclusion where

open import Agora.Conventions.Prelude
open import Agora.Conventions.Meta2.Macros
open import Agora.Conventions.Meta.Universe
-- open import Agora.Conventions.Prelude.Data.StrictId


record hasInclusion (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor inclusion
  field ιᵘ : A -> B

open hasInclusion {{...}} public

macro
  ι : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : hasInclusion A B}} -> SomeStructure
  ι = #structureOn ιᵘ


