-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Category.Construction.Id where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Data.Product.Definition
-- open import Agora.Data.Fin.Definition
-- open import Agora.Algebra.Monoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Morphism.Iso



private
  module _ {A : 𝒰 𝑖} where
    lem-1 : ∀{a b : A} {p : a ≡ b} -> p ∙-≡ refl-≡ ≡ p
    lem-1 {p = refl-≡} = refl-≡

    lem-2 : ∀{a b c d : A} {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} -> (p ∙-≡ q) ∙-≡ r ≡ p ∙-≡ (q ∙-≡ r)
    lem-2 {p = refl-≡} = refl-≡

    lem-3 : ∀{a b c : A} -> {p₀ p₁ : a ≡ b} {q₀ q₁ : b ≡ c} -> (p₀ ≡ p₁) -> (q₀ ≡ q₁) -> (p₀ ∙-≡ q₀ ≡ p₁ ∙-≡ q₁)
    lem-3 refl-≡ refl-≡ = refl-≡


module _ {A : 𝒰 𝑖} where

  isCategoryData:byId : isCategoryData A _≡_
  isCategoryData.isSetoid:Hom isCategoryData:byId = isSetoid:byId
  isCategoryData.id isCategoryData:byId           = refl-≡
  isCategoryData._◆_ isCategoryData:byId          = _∙-≡_
  isCategoryData.unit-l-◆ isCategoryData:byId     = incl refl-≡
  isCategoryData.unit-r-◆ isCategoryData:byId     = incl lem-1
  isCategoryData.unit-2-◆ isCategoryData:byId     = incl refl-≡
  isCategoryData.assoc-l-◆ isCategoryData:byId {f = p} = incl $ lem-2 {p = p}
  isCategoryData.assoc-r-◆ isCategoryData:byId {f = p} = incl $ sym-≡ (lem-2 {p = p})
  isCategoryData._◈_ isCategoryData:byId          = λ p q -> incl $ lem-3 ⟨ p ⟩ ⟨ q ⟩

  isCategory:byId : isCategory A
  isCategory.Hom isCategory:byId          = _≡_
  isCategory.HomData isCategory:byId = isCategoryData:byId
