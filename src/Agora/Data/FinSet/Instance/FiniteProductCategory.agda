
-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module Agora.Data.FinSet.Instance.FiniteProductCategory where

open import Agora.Conventions
open import Agora.Data.Product.Definition
open import Agora.Data.Sum.Definition
open import Agora.Data.Fin.Definition
open import Agora.Data.Universe.Instance.Setoid

open import Agora.Data.FinSet.Definition
open import Agora.Data.FinSet.Instance.Category


open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Limit.Specific.Product.Variant.Binary

-- open import Data.Fin.Base using (_↑ˡ_ ; _↑ʳ_)

open import Data.Fin using (remQuot ; combine)

instance
  isFinite:⊤-𝒰 : isFinite (⊤-𝒰 {𝑖 = 𝑖})
  isFinite:⊤-𝒰 = record { size = 1 ; index = const zero ; isIso:index = P }
    where
      P : _
      P = record { inverse-𝒰 = const tt ; inv-r-◆-𝒰 = λ {tt -> refl-≡} ; inv-l-◆-𝒰 = λ {zero -> refl-≡} }

⊤-𝐅𝐢𝐧𝐒𝐞𝐭 : 𝐅𝐢𝐧𝐒𝐞𝐭 𝑖
⊤-𝐅𝐢𝐧𝐒𝐞𝐭 = ⊤-𝒰 since isFinite:⊤-𝒰

intro-⊤-𝐅𝐢𝐧𝐒𝐞𝐭 : ∀{A : 𝐅𝐢𝐧𝐒𝐞𝐭 𝑖} -> FinSetHom A (⊤-𝐅𝐢𝐧𝐒𝐞𝐭 {𝑖 = 𝑗})
intro-⊤-𝐅𝐢𝐧𝐒𝐞𝐭 = (const tt) since tt

instance
  isTerminal:⊤-𝐅𝐢𝐧𝐒𝐞𝐭 : isTerminal (⊤-𝐅𝐢𝐧𝐒𝐞𝐭 {𝑖 = 𝑖})
  isTerminal:⊤-𝐅𝐢𝐧𝐒𝐞𝐭 = record { intro-⊤ = intro-⊤-𝐅𝐢𝐧𝐒𝐞𝐭 ; expand-⊤ = {!!} }

instance
  hasTerminal:𝐅𝐢𝐧𝐒𝐞𝐭 : hasTerminal (𝐅𝐢𝐧𝐒𝐞𝐭 𝑖)
  hasTerminal:𝐅𝐢𝐧𝐒𝐞𝐭 = record { ⊤ = ⊤-𝐅𝐢𝐧𝐒𝐞𝐭 }

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{Ap : isFinite A}} {{Bp : isFinite B}} where
  instance
    isFinite:×-𝒰 : isFinite (A × B)
    isFinite:×-𝒰 = record
      { size = size Ap *-ℕ size Bp
      ; index = λ (a , b) -> combine (index a) (index b)
      ; isIso:index = {!!}
      }

_⊓-𝐅𝐢𝐧𝐒𝐞𝐭_ : 𝐅𝐢𝐧𝐒𝐞𝐭 𝑖 -> 𝐅𝐢𝐧𝐒𝐞𝐭 𝑗 -> 𝐅𝐢𝐧𝐒𝐞𝐭 (𝑖 ､ 𝑗)
_⊓-𝐅𝐢𝐧𝐒𝐞𝐭_ A B = (⟨ A ⟩ ×-𝒰 ⟨ B ⟩) since isFinite:×-𝒰


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑖} {{Ap : isFinite A}} {{Bp : isFinite B}} where
  instance
    isProduct:⊓-𝐅𝐢𝐧𝐒𝐞𝐭 : isProduct ′ A ′ ′ B ′ (′ A ′ ⊓-𝐅𝐢𝐧𝐒𝐞𝐭 ′ B ′)
    isProduct:⊓-𝐅𝐢𝐧𝐒𝐞𝐭 = record
      { π₀ = fst since tt
      ; π₁ = snd since tt
      ; ⧼_⧽ = λ (f , g) -> (λ x -> ⟨ f ⟩ x , ⟨ g ⟩ x) since tt
      ; reduce-π₀ = refl-∼
      ; reduce-π₁ = refl-∼
      ; expand-π₀,π₁ = refl-∼
      ; isSetoidHom:⧼⧽ = {!!}
      }

instance
  hasProducts:𝐅𝐢𝐧𝐒𝐞𝐭 : hasProducts (𝐅𝐢𝐧𝐒𝐞𝐭 𝑖)
  hasProducts:𝐅𝐢𝐧𝐒𝐞𝐭 = record
    { _⊓_ = _⊓-𝐅𝐢𝐧𝐒𝐞𝐭_
    ; isProduct:⊓ = isProduct:⊓-𝐅𝐢𝐧𝐒𝐞𝐭
    }



