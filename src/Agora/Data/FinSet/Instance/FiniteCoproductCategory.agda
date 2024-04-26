
-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module Agora.Data.FinSet.Instance.FiniteCoproductCategory where

open import Agora.Conventions
open import Agora.Data.Product.Definition
open import Agora.Data.Sum.Definition
open import Agora.Data.Fin.Definition
open import Agora.Data.Universe.Instance.Setoid

open import Agora.Data.FinSet.Definition
open import Agora.Data.FinSet.Instance.Category


open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Limit.Specific.Coproduct.Variant.Binary

open import Data.Fin.Base using (_↑ˡ_ ; _↑ʳ_)

instance
  isFinite:⊥-𝒰 : isFinite (⊥-𝒰 {𝑖 = 𝑖})
  isFinite:⊥-𝒰 = record { size = 0 ; index = λ () ; isIso:index = P }
    where
      P : _
      P = record { inverse-𝒰 = λ () ; inv-r-◆-𝒰 = λ {()} ; inv-l-◆-𝒰 = λ () }

⊥-𝐅𝐢𝐧𝐒𝐞𝐭 : 𝐅𝐢𝐧𝐒𝐞𝐭 𝑖
⊥-𝐅𝐢𝐧𝐒𝐞𝐭 = ⊥-𝒰 since isFinite:⊥-𝒰

elim-⊥-𝐅𝐢𝐧𝐒𝐞𝐭 : ∀{A : 𝐅𝐢𝐧𝐒𝐞𝐭 𝑖} -> FinSetHom (⊥-𝐅𝐢𝐧𝐒𝐞𝐭 {𝑖 = 𝑗}) A
elim-⊥-𝐅𝐢𝐧𝐒𝐞𝐭 = (λ ()) since tt

instance
  isInitial:⊥-𝐅𝐢𝐧𝐒𝐞𝐭 : isInitial (⊥-𝐅𝐢𝐧𝐒𝐞𝐭 {𝑖 = 𝑖})
  isInitial:⊥-𝐅𝐢𝐧𝐒𝐞𝐭 = record { elim-⊥ = elim-⊥-𝐅𝐢𝐧𝐒𝐞𝐭 ; expand-⊥ = {!!} }

instance
  hasInitial:𝐅𝐢𝐧𝐒𝐞𝐭 : hasInitial (𝐅𝐢𝐧𝐒𝐞𝐭 𝑖)
  hasInitial:𝐅𝐢𝐧𝐒𝐞𝐭 = record { ⊥ = ⊥-𝐅𝐢𝐧𝐒𝐞𝐭 }


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{Ap : isFinite A}} {{Bp : isFinite B}} where
  instance
    isFinite:+-𝒰 : isFinite (A + B)
    isFinite:+-𝒰 = record
      { size = size Ap +-ℕ size Bp
      ; index = either (λ a -> index a ↑ˡ _) λ b -> _ ↑ʳ index b
      ; isIso:index = {!!}
      }

_⊔-𝐅𝐢𝐧𝐒𝐞𝐭_ : 𝐅𝐢𝐧𝐒𝐞𝐭 𝑖 -> 𝐅𝐢𝐧𝐒𝐞𝐭 𝑗 -> 𝐅𝐢𝐧𝐒𝐞𝐭 (𝑖 ､ 𝑗)
_⊔-𝐅𝐢𝐧𝐒𝐞𝐭_ A B = (⟨ A ⟩ +-𝒰 ⟨ B ⟩) since isFinite:+-𝒰


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑖} {{Ap : isFinite A}} {{Bp : isFinite B}} where
  instance
    isCoproduct:⊔-𝐅𝐢𝐧𝐒𝐞𝐭 : isCoproduct ′ A ′ ′ B ′ (′ A ′ ⊔-𝐅𝐢𝐧𝐒𝐞𝐭 ′ B ′)
    isCoproduct:⊔-𝐅𝐢𝐧𝐒𝐞𝐭 = record
      { ι₀ = left since tt
      ; ι₁ = right since tt
      ; ⦗_⦘ = λ (f , g) -> either ⟨ f ⟩ ⟨ g ⟩ since tt
      ; reduce-ι₀ = refl-∼
      ; reduce-ι₁ = refl-∼
      ; expand-ι₀,ι₁ = {!!}
      ; isSetoidHom:⦗⦘ = {!!}
      }

instance
  hasCoproducts:𝐅𝐢𝐧𝐒𝐞𝐭 : hasCoproducts (𝐅𝐢𝐧𝐒𝐞𝐭 𝑖)
  hasCoproducts:𝐅𝐢𝐧𝐒𝐞𝐭 = record
    { _⊔_ = _⊔-𝐅𝐢𝐧𝐒𝐞𝐭_
    ; isCoproduct:⊔ = isCoproduct:⊔-𝐅𝐢𝐧𝐒𝐞𝐭
    }


