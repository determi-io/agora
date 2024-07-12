-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

--
-- NOTE: This file is originally from the cubical std library.
--       (https://github.com/agda/cubical)
--       It was copied here to replace references to cubical paths,
--       since cubical agda files cannot currently be compiled to binaries.
--       All copyright belongs to the original authors.
--
-- See:
-- module Cubical.Data.List.Base where
--

module Agora.Conventions.Prelude.Data.List.Base where

open import Agora.Conventions.Proprelude.CubicalConventions
open import Agora.Conventions.Prelude.Data.Nat
open import Agora.Conventions.Prelude.Data.Nat.Literals

open import Agda.Builtin.List        public renaming (_∷_ to infixr 25 _∷_)
-- open import Cubical.Core.Everything
-- open import Cubical.Data.Nat
open import Data.List public using
  (
  )
  renaming
  (_++_ to infixr 25 _++_
  ; _∷ʳ_ to infixr 25 _∷ʳ_
  )

open import Data.List.Properties public using
  ()
  renaming
  ( ++-assoc to assoc-++-List
  ; ++-identityʳ to unit-r-++-List
  ; ++-identityˡ to unit-l-++-List
  )

module _ {ℓ} {A : Type ℓ} where

  -- infixr 25 _++_ _∷ʳ_

  [_] : A → List A
  [ a ] = a ∷ []

  -- _++_ : List A → List A → List A
  -- [] ++ ys = ys
  -- (x ∷ xs) ++ ys = x ∷ xs ++ ys

  rev : List A → List A
  rev [] = []
  rev (x ∷ xs) = rev xs ++ [ x ]

  -- _∷ʳ_ : List A → A → List A
  -- xs ∷ʳ x = xs ++ (x ∷ [])

  length : List A → ℕ
  length [] = 0
  length (x ∷ l) = 1 +-ℕ length l

  foldr : ∀ {ℓ'} {B : Type ℓ'} → (A → B → B) → B → List A → B
  foldr f b [] = b
  foldr f b (x ∷ xs) = f x (foldr f b xs)
