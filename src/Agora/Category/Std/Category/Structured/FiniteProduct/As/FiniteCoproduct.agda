
module Agora.Category.Std.Category.Structured.FiniteProduct.As.FiniteCoproduct where

open import Agora.Conventions hiding (_⊔_)
open import Agora.Setoid.Definition
open import Agora.Algebra.Monoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Opposite
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition
open import Agora.Category.Std.Limit.Specific.Product.Instance.Coproduct
open import Agora.Category.Std.Limit.Specific.Product.Variant.Binary


module _ {𝒞 : Category 𝑖} {{_ : hasFiniteProducts 𝒞}} where
  instance
    hasCoproducts:ᵒᵖ : hasCoproducts (𝒞 ᵒᵖ)
    hasCoproducts._⊔_ hasCoproducts:ᵒᵖ = _⊓_
    hasCoproducts.isCoproduct:⊔ hasCoproducts:ᵒᵖ = it

    hasInitial:ᵒᵖ : hasInitial (𝒞 ᵒᵖ)
    hasInitial.⊥ hasInitial:ᵒᵖ = ⊤
    hasInitial.isInitial:⊥ hasInitial:ᵒᵖ = it

  instance
    hasFiniteCoproducts:ᵒᵖ : hasFiniteCoproducts (𝒞 ᵒᵖ)
    hasFiniteCoproducts.hasInitial:this hasFiniteCoproducts:ᵒᵖ = hasInitial:ᵒᵖ
    hasFiniteCoproducts.hasCoproducts:this hasFiniteCoproducts:ᵒᵖ = hasCoproducts:ᵒᵖ






