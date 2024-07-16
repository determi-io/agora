-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.TypeTheory.STT.Definition where

open import Agora.Conventions hiding (m ; n ; _∙_ ; _∣_)
open import Agora.Data.Fin.Definition


record STT (𝑗 : 𝔏 ^ 3) : 𝒰 ( 𝑗 ⁺) where
  field Ctx : 𝒰 (𝑗 ⌄ 0)
  field Type : 𝒰 (𝑗 ⌄ 1)
  field Term : Ctx -> Type -> 𝒰 (𝑗 ⌄ 2)

open STT public


record Hom-STT (𝔄 : STT 𝑖) (𝔅 : STT 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field ⟪_∣_Ctx⟫ : Ctx 𝔄 -> Ctx 𝔅
  field ⟪_∣_Type⟫ : Type 𝔄 -> Type 𝔅
  field ⟪_∣_Term⟫ : ∀{Γ A} -> Term 𝔄 Γ A -> Term 𝔅 (⟪_∣_Ctx⟫ Γ) (⟪_∣_Type⟫ A)


open Hom-STT public

STTHom = Hom-STT

module _ {𝔄 : STT 𝑖} {𝔅 : STT 𝑗} {𝔇 : STT 𝑘} where
  _◆-STT_ : STTHom 𝔄 𝔅 -> STTHom 𝔅 𝔇 -> STTHom 𝔄 𝔇
  _◆-STT_ f g = record
    { ⟪_∣_Ctx⟫ = λ a -> ⟪ g ∣ ⟪ f ∣ a Ctx⟫ Ctx⟫
    ; ⟪_∣_Type⟫ = λ a -> ⟪ g ∣ ⟪ f ∣ a Type⟫ Type⟫
    ; ⟪_∣_Term⟫ = λ a -> ⟪ g ∣ ⟪ f ∣ a Term⟫ Term⟫
    }



