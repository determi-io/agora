
module Agora.Category.Std.Category.Subcategory.Full2 where

open import Agora.Conventions

open import Agora.Setoid
open import Agora.Set.Discrete
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} {X : 𝒰 𝑘} (ι : X -> 𝒞) where

  isCategory:FullSubcategory : isCategory {𝑗} X
  isCategory.Hom isCategory:FullSubcategory = λ a b -> Hom (ι a) (ι b)
  isCategory.isSetoid:Hom isCategory:FullSubcategory = {!!}
  isCategory.id isCategory:FullSubcategory = {!!}
  isCategory._◆_ isCategory:FullSubcategory = {!!}
  isCategory.unit-l-◆ isCategory:FullSubcategory = {!!}
  isCategory.unit-r-◆ isCategory:FullSubcategory = {!!}
  isCategory.unit-2-◆ isCategory:FullSubcategory = {!!}
  isCategory.assoc-l-◆ isCategory:FullSubcategory = {!!}
  isCategory.assoc-r-◆ isCategory:FullSubcategory = {!!}
  isCategory._◈_ isCategory:FullSubcategory = {!!}






