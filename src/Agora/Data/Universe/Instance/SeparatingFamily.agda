
module Agora.Data.Universe.Instance.SeparatingFamily where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Data.Universe.Definition
open import Agora.Category.Std.Category.Structured.SeparatingFamily
open import Agora.Data.Universe.Instance.Category


private
  sep : ∀ 𝑗 -> ∀{𝑖} -> ⊤-𝒰 {𝑗} -> 𝒰 𝑖
  sep _ = const ⊤-𝒰

instance
  isSeparatingFamily:const⊤ : isSeparatingFamily (𝐔𝐧𝐢𝐯 𝑖) (sep 𝑗)
  isSeparatingFamily.separate isSeparatingFamily:const⊤ ϕ ψ x = P
    where
      P : ϕ ∼ ψ
      P = λ i a → x {tt} (const a) i tt

module _ {𝑖} {𝑗} where
  instance
    hasSeparatingFamily:𝐔𝐧𝐢𝐯 : hasSeparatingFamily 𝑗 (𝐔𝐧𝐢𝐯 𝑖)
    hasSeparatingFamily:𝐔𝐧𝐢𝐯 = record
                                { separator = sep 𝑗
                                ; isSeparatingFamily:seperators = it
                                }



