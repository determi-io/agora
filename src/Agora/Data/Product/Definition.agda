-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Data.Product.Definition where

open import Agora.Conventions


macro
  _×_ : ∀{𝑖 𝑗 : 𝔏} {𝑘 𝑙 : 𝔏 ^ 2} -> (𝒰' 𝑖) [ 𝑙 ]→ (𝒰' 𝑗) [ 𝑘 ]→ SomeStructure
  _×_ = λstr A ↦ λstr B ↦ #structureOn (A ×-𝒰 B)
  infixr 40 _×_


-- The product for haskell

record _×~_ (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor _,_
  field fst : A
  field snd : B


{-# FOREIGN GHC type AgdaProduct a b = (,) #-}
-- {-# FOREIGN GHC makeProduct a b = (a,b) #-}
{-# COMPILE GHC _×~_ = data AgdaProduct ((,)) #-}

module _ {A : 𝒰 𝑖} {A' : 𝒰 𝑘} {B : 𝒰 𝑗} {B' : 𝒰 𝑙} where
  map-×-𝒰 : ((A -> A') ×-𝒰 (B -> B')) -> (A ×-𝒰 B) -> (A' ×-𝒰 B')
  map-×-𝒰 (f , g) (a , b) = f a , g b

--------------------------------------------------------------
-- The Instance Product

record _×-AgdaInstance_ (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor intro-×-AgdaInstance
  field {{fst-×-AgdaInstance}} : A
  field {{snd-×-AgdaInstance}} : B

open _×-AgdaInstance_ {{...}} public


--------------------------------------------------------------
-- The 0-ary product

macro
  𝟙 : ∀ {𝑖} -> SomeStructure
  𝟙 {𝑖} = #structureOn (⊤-𝒰 {𝑖})

isProp:⊤-𝒰 : ∀{a b : ⊤-𝒰 {𝑖}} -> a ≡ b
isProp:⊤-𝒰 {a = tt} {tt} = refl-≡

-- isSet:⊤-𝒰 : ∀{a b : ⊤-𝒰 {𝑖}} {p q : a ≡ b} -> p ≡ q
-- isSet:⊤-𝒰 {p = refl-≡} {q} = {!!}

instance
  isDiscrete:⊤-𝒰 : isDiscrete (⊤-𝒰 {𝑖})
  isDiscrete:⊤-𝒰 = record { _≟-Str_ = λ {tt tt → right refl-≡} }

instance
  IShow:⊤-𝒰 : IShow (⊤-𝒰 {𝑖})
  IShow:⊤-𝒰 = record { show = const "()" }

