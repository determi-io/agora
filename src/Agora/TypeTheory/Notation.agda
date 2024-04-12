
module Agora.TypeTheory.Notation where

open import Agora.Conventions hiding (m ; n ; _∙_ ; _∣_)


record isTypeTheory {𝑘} (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑘 ⁺) where
  field {CtxType} : A -> 𝒰 𝑘
  field Ctx : {{a : A}} -> CtxType a
  [_]-Ctx : (a : A) -> CtxType a
  [_]-Ctx a = Ctx {{a}}
  field {TypeType} : A -> 𝒰 𝑘
  field ⊢Type : {{a : A}} -> TypeType a
  field {TurnstyleType} : A -> 𝒰 𝑘
  field _⊢_ : {{a : A}} -> TurnstyleType a
  _▻_⊢_ : (a : A) -> TurnstyleType a
  _▻_⊢_ a = _⊢_ {{a}}

open isTypeTheory {{...}} public

