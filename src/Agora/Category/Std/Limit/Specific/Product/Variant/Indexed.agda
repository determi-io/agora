
module Agora.Category.Std.Limit.Specific.Product.Variant.Indexed where

open import Agora.Conventions hiding (_⊔_)
open import Agora.Setoid.Definition
-- open import Agora.Data.Fin.Definition
-- open import Agora.Data.Product.Definition
open import Agora.Data.Sum.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Notation.Associativity


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where

  record isIndexedProduct {I : 𝒰 𝑘} (aᵢ : I -> 𝒞) (x : 𝒞) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    field πᵢ : ∀ i -> x ⟶ aᵢ i
    field ⧼_⧽ᵢ : ∀{y} -> (∀ i -> y ⟶ aᵢ i) -> y ⟶ x
    field reduce-πᵢ : ∀{y} -> (f : ∀ i -> y ⟶ aᵢ i) -> ∀ i -> ⧼ f ⧽ᵢ ◆ πᵢ i  ∼ f i
    field expand-πᵢ : ∀{y} -> (f : y ⟶ x) -> f ∼ ⧼ (λ i -> f ◆ πᵢ i) ⧽ᵢ

    product-syntax = ⧼_⧽ᵢ
    syntax product-syntax (λ i -> f) = ⧼ f ⧽[ i ]

  open isIndexedProduct {{...}} public

record hasIndexedProducts (X : 𝒰 𝑘) (I : X -> 𝒰 𝑗) (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ 𝑘 ､ 𝑗) where
  infixl 80 ⨅ᵢ
  field ⨅ᵢ : ∀{x} -> (I x -> ⟨ 𝒞 ⟩) -> ⟨ 𝒞 ⟩
  field {{isIndexedProduct:⨅ᵢ}} : ∀{x} -> {F : I x -> ⟨ 𝒞 ⟩} -> isIndexedProduct F (⨅ᵢ F)

  syntax ⨅ᵢ {x = X} (λ i -> F) = ⨅[ i ∶ X ] F

open hasIndexedProducts {{...}} public

-- See NOTE in Coproducts
{-
record hasIndexedProducts (I : 𝒰 𝑗) (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ 𝑗) where
  infixl 80 ⨅ᵢ
  field ⨅ᵢ : (I -> ⟨ 𝒞 ⟩) -> ⟨ 𝒞 ⟩
  field {{isIndexedProduct:⨅ᵢ}} : ∀{x : I -> ⟨ 𝒞 ⟩} -> isIndexedProduct x (⨅ᵢ x)

  syntax ⨅ᵢ (λ i -> X) = ⨅[ i ] X

open hasIndexedProducts {{...}} public

module _ (𝑗 : 𝔏) (𝒞 : Category 𝑖) where
  hasAllIndexedProducts : ∀{I : 𝒰 𝑗} -> 𝒰 _
  hasAllIndexedProducts {I} = hasIndexedProducts I 𝒞
-}



{-
record hasAllIndexedProducts (𝑗 : 𝔏) (𝒞 : Category 𝑖): 𝒰 (𝑖 ､ 𝑗 ⁺) where
  infixl 80 ⨅ᵢ
  field ⨅ᵢ : ∀{I : 𝒰 𝑗} -> (I -> ⟨ 𝒞 ⟩) -> ⟨ 𝒞 ⟩
  field {{isIndexedProduct:⨅ᵢ}} : ∀{I : 𝒰 𝑗} -> ∀{x : I -> ⟨ 𝒞 ⟩} -> isIndexedProduct x (⨅ᵢ x)

  syntax ⨅ᵢ (λ i -> X) = ⨅[ i ] X

open hasAllIndexedProducts {{...}} public
-}

