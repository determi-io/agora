-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Order.WellFounded.Construction.Lexicographic where

{-

open import Agora.Conventions
open import Agora.Set.Induction.WellFounded
open import Agora.Data.Product.Definition
open import Agora.Order.WellFounded.Definition

record Lexicographic (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor _,_
  field fst : A
  field snd : B

module _ (A : 𝒰 𝑖) (B : 𝒰 𝑗) where
  macro Lexi = #structureOn (Lexicographic A B)


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} (R : A -> A -> 𝒰 𝑘) (S : B -> B -> 𝒰 𝑙) where
  data ≪-Lexi : (Lexi A B) -> (Lexi A B) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ､ 𝑙) where
    first : ∀{a0 b0 a1 b1} -> R a0 a1 -> ≪-Lexi (a0 , b0) (a1 , b1)
    second : ∀{a0 b0 b1} -> S b0 b1 -> ≪-Lexi (a0 , b0) (a0 , b1)

  private
    T = ≪-Lexi

  module _ (p : WellFounded R) (q : WellFounded S) where
    private

      lem-3 : ∀ a b -> Acc R a -> Acc S b -> ∀ ab1 -> T ab1 (a , b) -> Acc T ab1
      lem-3 a b (racc) (acc sacc) ab1 (second x) = acc (lem-3 _ _ racc (sacc _ x))
      lem-3 a b (acc racc) (acc sacc) ab1 (first x) = acc (lem-3 _ _ (racc _ x) (q _))

      lem-1 : ∀ x -> Acc T x
      lem-1 (a0 , b0) = acc (lem-3 a0 b0 (p a0) (q b0))

    WellFounded:Lexi : WellFounded T
    WellFounded:Lexi = lem-1


module _ {A : 𝒰 𝑖} {{_ : isWF 𝑗 A}}
         {B : 𝒰 𝑘} {{_ : isWF 𝑙 B}} where
  instance
    isWF:Lexi : isWF _ (Lexi A B)
    isWF:Lexi = record { _≪_ = ≪-Lexi _≪_ _≪_ ; wellFounded = WellFounded:Lexi _≪_ _≪_ wellFounded wellFounded }

  module _ {{_ : isWFT ′ A ′}} {{_ : isWFT ′ B ′}} where
    instance
      isWFT:Lexi : isWFT (Lexi A B)
      isWFT:Lexi = {!!}

    module _ {{_ : isWFT0 ′ A ′}} where
      instance
        isWFT0:Lexi : isWFT0 (Lexi A B)
        isWFT0:Lexi = {!!}


-}

