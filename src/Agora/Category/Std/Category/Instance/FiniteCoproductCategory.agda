
module Agora.Category.Std.Category.Instance.FiniteCoproductCategory where

open import Agora.Conventions
open import Agora.Setoid
-- open import Agora.Data.Product.Definition
open import Agora.Data.Sum.Definition
open import Agora.Data.Lift.Definition
-- open import Agora.Data.Fin.Definition
-- open import Agora.Algebra.Monoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Category.Construction.Id
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Agora.Category.Std.Limit.Specific.Product
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Constant
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Natural.Instance.Setoid
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Construction.Coproduct


module _ {𝒞 𝒟 : 𝐂𝐚𝐭 𝑖} where
  instance
    isCoproduct:+-𝐂𝐚𝐭 : isCoproduct 𝒞 𝒟 (𝒞 + 𝒟)
    isCoproduct.ι₀ isCoproduct:+-𝐂𝐚𝐭 = {!!}
    isCoproduct.ι₁ isCoproduct:+-𝐂𝐚𝐭 = {!!}
    isCoproduct.⦗ isCoproduct:+-𝐂𝐚𝐭 ⦘ = {!!}
    isCoproduct.reduce-ι₀ isCoproduct:+-𝐂𝐚𝐭 = {!!}
    isCoproduct.reduce-ι₁ isCoproduct:+-𝐂𝐚𝐭 = {!!}
    isCoproduct.expand-ι₀,ι₁ isCoproduct:+-𝐂𝐚𝐭 = {!!}
    isCoproduct.isSetoidHom:⦗⦘ isCoproduct:+-𝐂𝐚𝐭 = {!!}



