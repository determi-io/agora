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
-- module Cubical.Data.Int.Base where
--

-- open import Cubical.Core.Everything
-- open import Cubical.Data.Nat

module Agora.Conventions.Prelude.Data.Int.Base where

open import Agora.Conventions.Proprelude.CubicalConventions
open import Agora.Conventions.Prelude.Data.Nat.Base
open import Agora.Conventions.Prelude.Data.Nat.Properties
open import Agora.Conventions.Proprelude
open import Agora.Conventions.Prelude.Data.StrictId
open import Agora.Conventions.Prelude.Classes.EquivalenceRelation
open import Agora.Conventions.Prelude.Classes.Setoid

open import Agda.Builtin.Int public

-- data Int : Type₀ where
--   pos    : (n : ℕ) → Int
--   negsuc : (n : ℕ) → Int

-- {-# BUILTIN INTEGER       Int    #-}
-- {-# BUILTIN INTEGERPOS    pos    #-}
-- {-# BUILTIN INTEGERNEGSUC negsuc #-}


_∼-Int_ : Int -> Int -> 𝒰₀
_∼-Int_ = _≡_

instance
  isEquivRel:∼-Int : isEquivRel _∼-Int_
  isEquivRel:∼-Int = isEquivRel:≡

instance
  isSetoid:Int : isSetoid Int
  isSetoid:Int = isSetoid:byId

neg : (n : ℕ) → Int
neg zero = pos zero
neg (suc n) = negsuc n

sucInt : Int → Int
sucInt (pos n)          = pos (suc n)
sucInt (negsuc zero)    = pos zero
sucInt (negsuc (suc n)) = negsuc n

predInt : Int → Int
predInt (pos zero)    = negsuc zero
predInt (pos (suc n)) = pos n
predInt (negsuc n)    = negsuc (suc n)

-- Natural number and negative integer literals for Int

-- open import Cubical.Data.Nat.Literals public
open import Agora.Conventions.Prelude.Data.Nat.Literals public


instance
  fromNatInt : HasFromNat Int
  fromNatInt = record { Constraint = λ _ → 𝟙-𝒰 ; fromNat = λ n → pos n }

instance
  fromNegInt : HasFromNeg Int
  fromNegInt = record { Constraint = λ _ → 𝟙-𝒰 ; fromNeg = λ n → neg n }
