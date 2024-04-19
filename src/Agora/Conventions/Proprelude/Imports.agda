-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

-- {-# OPTIONS --cubical --no-import-sorts #-}

module Agora.Conventions.Proprelude.Imports where

open import Agda.Primitive public using (lzero)
  renaming
  (Level to 𝔏; lsuc to _⁺ ; Setω to 𝒰ω ; Set to 𝒰' ; Prop to CompProp ; _⊔_ to join-𝔏 ;
  SSet to S𝒰
  )


open import Agda.Builtin.String public
  renaming (String to Text)

String = Text





open import Data.Product using (Σ ; Σ-syntax) renaming (_×_ to _×-𝒰_ ; _,_ to infixr 28 _,_ ; proj₁ to fst ; proj₂ to snd) public



