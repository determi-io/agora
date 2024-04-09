
module Agora.Setoid.Power.Definition where

open import Agora.Conventions
open import Agora.Data.Prop.Definition
open import Agora.Data.Product.Definition
open import Agora.Setoid.Definition
open import Agora.Setoid.Instance.Category


-- record PowerSetoid (A : 𝐒𝐭𝐝 𝑖) : 𝒰 (𝑖 ⁺) where
--   field El : Subsetoid A

PowerSetoid = Subsetoid

module _ (A : 𝐒𝐭𝐝 𝑖) where
  macro
    𝒫-𝐒𝐭𝐝 = #structureOn (PowerSetoid A)

instance
  hasPower:𝐒𝐭𝐝 : hasPower (𝐒𝐭𝐝 𝑖) (𝒰 (fst 𝑖 ⁺ ⊔ snd 𝑖))
  hasPower:𝐒𝐭𝐝 = record { 𝒫ᵘ = Subsetoid }




