-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Category.Instance.Category where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Data.Universe.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Natural.Instance.Setoid
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Instance.2Category

open import Agora.Category.Std.Category.Instance.CategoryLike public


all : 𝔏 ^ 3 -> 𝔏
all (i , j , k) = i ⊔ j ⊔ k



instance
  isCategory:Category : ∀{𝑗 : 𝔏 ^ 3} -> isCategory (Category 𝑗)
  isCategory.Hom isCategory:Category = Functor
  isCategory.isSetoid:Hom (isCategory:Category {𝑗}) = it
  isCategory.id isCategory:Category = id-𝐂𝐚𝐭
  isCategory._◆_ isCategory:Category F G = (F ◆-𝐂𝐚𝐭 G)
  isCategory.unit-l-◆ isCategory:Category = unit-l-◆-𝐂𝐚𝐭
  isCategory.unit-r-◆ isCategory:Category = unit-r-◆-𝐂𝐚𝐭
  isCategory.unit-2-◆ isCategory:Category = unit-r-◆-𝐂𝐚𝐭
  isCategory.assoc-l-◆ isCategory:Category {f = f} {g} {h} = assoc-l-◆-𝐂𝐚𝐭 {F = f} {g} {h}
  isCategory.assoc-r-◆ isCategory:Category {f = f} {g} {h} = assoc-l-◆-𝐂𝐚𝐭 {F = f} {g} {h} ⁻¹
  isCategory._◈_ isCategory:Category = _≀◆≀-𝐂𝐚𝐭_

instance
  isSetoid:Category : isSetoid (𝐂𝐚𝐭 𝑖)
  isSetoid:Category = isSetoid:byCategory


open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Constant

instance
  is2Category:𝐂𝐚𝐭 : is2Category (𝐂𝐚𝐭 𝑖)
  is2Category.cell is2Category:𝐂𝐚𝐭 = λ a b -> isCategory:Functor
  is2Category.isFunctor:Comp is2Category:𝐂𝐚𝐭 = isFunctor:Comp-𝐂𝐚𝐭
  is2Category.isFunctor:Id is2Category:𝐂𝐚𝐭 = isFunctor:const


