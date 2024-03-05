-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Order.Totalorder where

open import Agora.Conventions
-- open import Agora.Category.Definition
-- open import Agora.Category.Instance.Set.Definition
-- open import Agora.Type

open import Agora.Setoid.Definition

open import Agora.Order.Preorder

-- module _ {𝑖 : 𝔏 ^ 3} where
--   record isPartialorder (A : Preorder 𝑖) : 𝒰 𝑖 where
--    field antisym : ∀{a b : ⟨ A ⟩} -> (a ≤ b) -> (b ≤ a) -> a ∼ b

-- Partialorder : (𝑖 : 𝔏 ^ 3) -> 𝒰 _
-- Partialorder 𝑖 = Preorder 𝑖 :& isPartialorder




data Trichotomy' (A : Preorder 𝑖) (a b : ⟨ A ⟩) : 𝒰 𝑖 where
  lt : a ⋦ b -> Trichotomy' A a b
  eq : a ∼ b -> Trichotomy' A a b
  gt : b ⋦ a -> Trichotomy' A a b

case-Trichotomy_of : {A : Preorder 𝑖} {a b : ⟨ A ⟩} -> Trichotomy' A a b -> {P : 𝒰 𝑗} -> (a ⋦ b -> P) -> (a ∼ b -> P) -> (b ⋦ a -> P) -> P
case-Trichotomy lt x of a b c = a x
case-Trichotomy eq x of a b c = b x
case-Trichotomy gt x of a b c = c x



module _ {𝑖 : 𝔏 ^ 3} where
  record isTotalorder⁻ (A : Partialorder 𝑖) : 𝒰 𝑖 where
    field total⁻ : ∀(a b : ⟨ A ⟩) -> (a ≰ b) -> b ≤ a

  open isTotalorder⁻ {{...}} public

  record isTotalorder⁺ (A : Partialorder 𝑖) : 𝒰 𝑖 where
    field total⁺ : ∀(a b : ⟨ A ⟩) -> Trichotomy' ′ ⟨ A ⟩ ′ a b
    -- (a ≤ b) +-𝒰 b ≤ a

  open isTotalorder⁺ {{...}} public

Totalorder⁻ : (𝑖 : 𝔏 ^ 3) -> 𝒰 _
Totalorder⁻ 𝑖 = Preorder 𝑖 :& isPartialorder :& isTotalorder⁻

Totalorder⁺ : (𝑖 : 𝔏 ^ 3) -> 𝒰 _
Totalorder⁺ 𝑖 = Preorder 𝑖 :& isPartialorder :& isTotalorder⁺








{-
module _ {𝑗 : 𝔏 ^ 3} where
  -- data OrderingDecision {A : 𝒰 _} {{_ : Preorder 𝑗 on A}} (a b : A) : 𝒰 𝑗 where
  data OrderingDecision (A : Totalorder 𝑗) (a b : ⟨ A ⟩) : 𝒰 𝑗 where
    LT : a < b -> OrderingDecision A a b
    EQ : a ∼ b -> OrderingDecision A a b
    GT : b < a -> OrderingDecision A a b

module _ {𝑖 : 𝔏 ^ 3} where
  record isDecidable-Totalorder (A : Totalorder 𝑖) : 𝒰 𝑖 where
    field compare : ∀(a b : ⟨ A ⟩) -> OrderingDecision A a b

  open isDecidable-Totalorder {{...}} public
-}
