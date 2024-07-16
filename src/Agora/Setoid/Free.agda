-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Setoid.Free where

open import Agora.Conventions
open import Agora.Data.Prop.Definition
open import Agora.Data.Product.Definition
open import Agora.Setoid.Definition



module _ {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) where
  data RST : A -> A -> 𝒰 (𝑖 ､ 𝑗) where
    incl : ∀{a b} -> R a b -> RST a b
    refl-RST : ∀{a} -> RST a a
    sym-RST : ∀{a b} -> RST a b -> RST b a
    _∙-RST_ : ∀{a b c} -> RST a b -> RST b c -> RST a c


module _ {A : 𝒰 𝑖} where
  isSetoid:byFree : (R : A -> A -> 𝒰 𝑗) -> isSetoid A
  isSetoid:byFree R = isSetoid:byDef (RST R) refl-RST sym-RST _∙-RST_


-- [Hide]
module _ {A : 𝒰 𝑖} {R : A -> A -> 𝒰 𝑗} {X : 𝒰 𝑘} {{_ : isSetoid {𝑙} X}} where
  rec-RST : {f : A -> X} (F : ∀{a b} -> R a b -> f a ∼ f b) -> ∀{a b} -> RST R a b -> f a ∼ f b
  rec-RST F (incl x) = F x
  rec-RST F refl-RST = refl
  rec-RST F (sym-RST p) = sym (rec-RST F p)
  rec-RST F (p ∙-RST q) = rec-RST F p ∙ rec-RST F q
-- //



