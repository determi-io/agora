-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Data.Fin.Definition where

open import Agora.Conventions
open import Agora.Data.Product.Definition
open import Agora.Data.Sum.Definition
open import Data.Nat renaming (_+_ to _+-ℕ_ ; _*_ to _*-ℕ_)
open import Data.Fin hiding (_+_ ; splitAt ; quotRem ; remQuot)
open import Data.Fin using (Fin ; suc ; zero) public


module _ {A : 𝒰 𝑖} where

  private
    ---------------------------------------
    -- from the std lib:
    --
    -- splitAt m "i" = inj₁ "i"      if i < m
    --                 inj₂ "i - m"  if i ≥ m
    -- This is dual to splitAt from Data.Vec.

    splitAt : ∀ m {n} → Fin (m +-ℕ n) → Fin m +-𝒰 Fin n
    splitAt zero    i       = right i
    splitAt (suc m) zero    = left zero
    splitAt (suc m) (suc i) = map-+-𝒰 suc (λ x -> x) (splitAt m i)

    -- quotRem k "i" = "i % k" , "i / k"
    -- This is dual to group from Data.Vec.

    quotRem : ∀ n → Fin (m *-ℕ n) → Fin n × Fin m
    quotRem {suc m} n i with splitAt n i
    ... | left j = j , zero
    ... | right j = map-×-𝒰 ((λ x -> x) , suc) (quotRem {m} n j)

    -- a variant of quotRem the type of whose result matches the order of multiplication
  remQuot : ∀ n → Fin (m *-ℕ n) → Fin m × Fin n
  remQuot i x = let a , b = (quotRem i x)
                in b , a

  caseᶠⁱⁿ_of : Fin (m +-ℕ n) -> (Fin m -> A) -> (Fin n -> A) -> A
  caseᶠⁱⁿ_of x f g = case splitAt _ x of f g

  ⦗_⦘ᶠⁱⁿ : (Fin m -> A) × (Fin n -> A) -> Fin (m +-ℕ n) -> A
  ⦗_⦘ᶠⁱⁿ (f , g) x = caseᶠⁱⁿ x of f g

  tupleᶠⁱⁿ_of : Fin (m *-ℕ n) -> (Fin m -> Fin n -> A) -> A
  tupleᶠⁱⁿ_of x f = let (a , b) = (remQuot _ x) in f a b




