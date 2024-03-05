-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Conventions.Impure where

open import Agora.Conventions.Prelude
open import Agora.Conventions.Meta

postulate
  FilePath : 𝒰₀

{-# COMPILE GHC FilePath as FilePath #-}


-----------------------------------------
-- reflection related

postulate
  FQName : 𝒰₀
  stringToFQName : String -> FQName

{-# COMPILE GHC FQName as Text #-}


