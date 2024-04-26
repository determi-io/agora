
{-# OPTIONS --allow-unsolved-metas #-}

module Agora.Category.Std.Category.Structured.FiniteProduct.Definition where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Data.Fin.Definition
open import Agora.Data.FinSet.Definition
open import Agora.Data.FinSet.Instance.Category
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Limit.Specific.Product
open import Agora.Category.Std.Limit.Specific.Product.Variant.Indexed

open import Data.Fin using (Fin ; suc ; zero)

FiniteProductCategory : ∀ 𝑖 -> 𝒰 _
FiniteProductCategory 𝑖 = Category 𝑖 :& hasFiniteProducts


module _ {𝒞 : 𝒰 _} {{_ : FiniteProductCategory 𝑖 on 𝒞}} where
  ⨅ᶠⁱⁿ : ∀{n} -> (F : Fin n -> 𝒞) -> 𝒞
  ⨅ᶠⁱⁿ {zero} F = ⊤
  ⨅ᶠⁱⁿ {suc n} F = F zero ⊓ (⨅ᶠⁱⁿ (λ i -> F (suc i)))

  syntax ⨅ᶠⁱⁿ {n = n} (λ x -> F) = ⨅ᶠⁱⁿ x ∈ n , F

  ⨅ᵢ-𝐅𝐢𝐧𝐒𝐞𝐭 : ∀(X : 𝐅𝐢𝐧𝐒𝐞𝐭 𝑗) -> (F : ⟨ X ⟩ -> 𝒞) -> 𝒞
  ⨅ᵢ-𝐅𝐢𝐧𝐒𝐞𝐭 X F = ⨅ᶠⁱⁿ λ (i : Fin (size (of X))) -> F (index⁻¹ i)

  instance
    has𝐅𝐢𝐧𝐒𝐞𝐭IndexedProducts:FiniteProductCategory : hasIndexedProducts (𝐅𝐢𝐧𝐒𝐞𝐭 𝑗) (λ X -> ⟨ X ⟩) ′ 𝒞 ′
    has𝐅𝐢𝐧𝐒𝐞𝐭IndexedProducts:FiniteProductCategory = record
      { ⨅ᵢ = λ {X} -> ⨅ᵢ-𝐅𝐢𝐧𝐒𝐞𝐭 X
      ; isIndexedProduct:⨅ᵢ = {!!}
      }





