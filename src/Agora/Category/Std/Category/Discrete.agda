
module Agora.Category.Std.Category.Discrete where

open import Agora.Conventions
-- open import Agora.Data.Prop.Definition
-- open import Agora.Data.Product.Definition
open import Agora.Setoid.Definition
open import Agora.Setoid.Discrete
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition


module _ {A : 𝒰 𝑖} where
  isCategory:byDiscrete : isCategory {𝑖 , 𝑖} A
  isCategory.Hom isCategory:byDiscrete = λ a b -> a ≡ b
  isCategory.isSetoid:Hom isCategory:byDiscrete = isSetoid:byDiscrete
  isCategory.id isCategory:byDiscrete = refl-≡
  isCategory._◆_ isCategory:byDiscrete = _∙-≡_
  isCategory.unit-l-◆ isCategory:byDiscrete = {!!}
  isCategory.unit-r-◆ isCategory:byDiscrete = {!!}
  isCategory.unit-2-◆ isCategory:byDiscrete = {!!}
  isCategory.assoc-l-◆ isCategory:byDiscrete = {!!}
  isCategory.assoc-r-◆ isCategory:byDiscrete = {!!}
  isCategory._◈_ isCategory:byDiscrete = {!!}


module _ {A : 𝒰 𝑖} {ℬ : Category 𝑗} {f : A -> ⟨ ℬ ⟩} where
  isFunctor:byDiscrete : isFunctor (A since isCategory:byDiscrete) ℬ f
  isFunctor.map isFunctor:byDiscrete {a} {b} p = transport (λ i -> f a ⟶ f (p i)) id
  isFunctor.isSetoidHom:map isFunctor:byDiscrete = {!!}
  isFunctor.functoriality-id isFunctor:byDiscrete = {!!}
  isFunctor.functoriality-◆ isFunctor:byDiscrete = {!!}


