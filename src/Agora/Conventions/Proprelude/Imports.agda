
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




-- open import Cubical.Foundations.Prelude
--   hiding (Type ; Lift ; lift ; lower ; isGroupoid)
--   renaming (refl to refl-Path ; sym to sym-Path ; _∙_ to trans-Path ; _∎ to _∎-Path ;
--             cong₂ to cong₂-Path ;
--             _∧_ to _⋏_ ; _∨_ to _⋎_)
--   public

open import Data.Product renaming (_×_ to _×-𝒰_ ; proj₁ to fst ; proj₂ to snd) public


