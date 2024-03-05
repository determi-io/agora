-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Workspace.Temp1 where

open import Agora.Conventions
open import Agora.Data.Prop.Definition
open import Agora.Data.Product.Definition


module Test1 where

  record isDefault (A : 𝒰 𝑖) (myProp : A -> A -> 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
    -- field myProp : A -> A -> 𝒰 𝑖
    -- field val : A
    field valp : ∀ {a : A} -> myProp a a

  open isDefault {{...}} using (valp) public


  -- module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isDefault A}} {{_ : isDefault B}} where
    -- instance
    --   isDefault:× : isDefault (A ×-𝒰 B)
    --   isDefault:× = {!!}

    -- aD : ∀{A B : 𝒰 𝑖} -> {{_ : isDefault A}} -> {{_ : isDefault B}} -> isDefault (A ×-𝒰 B)
    -- aD = {!!}

  mytest : ∀{A B : 𝒰 𝑖} -> ∀ {myProp} {myProp2} -> {{Ax : isDefault A myProp}}
          -> {{ _ : isDefault B myProp2}} -> (a : A) -> myProp a a
  mytest a = valp

module Test2 where

  record isDefault (A : 𝒰 𝑖) (myProp : A -> A -> 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
    -- field myProp : A -> A -> 𝒰 𝑖
    -- field val : A
    field valp : ∀ {a : A} -> myProp a a

  open isDefault {{...}} using (valp) public

  record isDefault' (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
    field myProp : A -> A -> 𝒰 𝑖
    field {{other}} : isDefault A myProp

  open isDefault' {{...}} using (myProp ; other) public
  -- open isDefault' using (other)


  mytest : ∀{A B : 𝒰 𝑖} -> ∀ {myProp} {myProp2} -> {{Ax : isDefault A myProp}}
          -> {{ _ : isDefault B myProp2}} -> (a : A) -> myProp a a
  mytest a = valp

  mytest2 : ∀{A B : 𝒰 𝑖} -> {{Ax : isDefault' A}}
          -> {{ _ : isDefault' B}} -> (a : A) -> myProp a a
  mytest2 a = valp





