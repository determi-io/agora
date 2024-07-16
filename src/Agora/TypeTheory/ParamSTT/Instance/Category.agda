-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module Agora.TypeTheory.ParamSTT.Instance.Category where

open import Agora.Conventions hiding (m ; n ; _∙_ ; _∣_)
open import Agora.Data.Fin.Definition
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition
open import Agora.Category.Std.Category.Definition



module _ {𝔄 : ParamSTT 𝑖} {𝔅 : ParamSTT 𝑗} {𝔇 : ParamSTT 𝑘} where
  _◆-ParamSTT_ : ParamSTTHom 𝔄 𝔅 -> ParamSTTHom 𝔅 𝔇 -> ParamSTTHom 𝔄 𝔇
  _◆-ParamSTT_ f g = (λ x -> ⟨ g ⟩ (⟨ f ⟩ x) ) since record
    { param = λ A p -> param _ (param _ p)
    ; subparam = λ A p -> subparam _ (subparam _ p)
    ; runAt = λ A x -> runAt _ x ◆-STT (runAt _ (subparam _ x))
    }

  infixl 30 _◆-ParamSTT_



instance
  isCategoryData:ParamSTT : isCategoryData (ParamSTT 𝑖) (ParamSTTHom)
  isCategoryData:ParamSTT = record
    { isSetoid:Hom = isSetoid:ParamSTTHom
    ; id = {!!}
    ; _◆_ = _◆-ParamSTT_
    ; unit-l-◆ = {!!}
    ; unit-r-◆ = {!!}
    ; unit-2-◆ = {!!}
    ; assoc-l-◆ = {!!}
    ; assoc-r-◆ = {!!}
    ; _◈_ = {!!}
    }

instance
  isCategory:ParamSTT : isCategory (ParamSTT 𝑖)
  isCategory:ParamSTT = record { Hom = ParamSTTHom }


