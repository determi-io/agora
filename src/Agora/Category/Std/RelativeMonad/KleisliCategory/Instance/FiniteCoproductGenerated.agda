
module Agora.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductGenerated where

open import Agora.Conventions hiding (_⊔_)

open import Agora.Setoid
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Functor.EssentiallySurjective
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.RelativeMonad.Definition
open import Agora.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition
open import Agora.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Agora.Category.Std.Category.Structured.FiniteCoproductGenerated
open import Agora.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory

open import Agora.Data.List.Variant.Binary.Natural
open import Agora.Data.List.Variant.Binary.Instance.Functor
open import Agora.Data.List.Variant.Binary.Definition
open import Agora.Data.List.Variant.Binary.Instance.Monoid
open import Agora.Data.List.Variant.Binary.Element.Definition
open import Agora.Data.List.Variant.Binary.ElementSum.Definition
open import Agora.Data.List.Variant.Binary.ElementSum.Instance.Category
-- open import Agora.Data.Indexed.Duplicate
open import Agora.Data.Indexed.Definition
open import Agora.Data.Indexed.Instance.Monoid
open import Agora.Data.FiniteIndexed.Definition
open import Agora.Category.Std.Category.Subcategory.Full
open import Agora.Category.Std.Morphism.Iso


module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} {𝒟 : Category 𝑗} {{_ : hasFiniteCoproducts 𝒟}} where
  module _ {J : Functor 𝒞 𝒟} {T : RelativeMonad J} {{_ : isFiniteCoproductPreserving J}} where

    module _ {{_ : isFiniteCoproductGenerated 𝑘 ′ ⟨ 𝒞 ⟩ ′}} where

      instance
        isFiniteCoproductGenerated:𝐑𝐞𝐊𝐥𝐬 : isFiniteCoproductGenerated 𝑘 (𝐑𝐞𝐊𝐥𝐬 T)
        isFiniteCoproductGenerated:𝐑𝐞𝐊𝐥𝐬 = isFiniteCoproductGenerated:byIsFiniteCoproductPreserving ι-𝐑𝐞𝐊𝐥𝐬



