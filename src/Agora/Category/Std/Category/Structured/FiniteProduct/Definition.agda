
module Agora.Category.Std.Category.Structured.FiniteProduct.Definition where

open import Agora.Conventions
open import Agora.Setoid.Definition
-- open import Agora.Data.Fin.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Limit.Specific.Product

open import Data.Fin using (Fin ; suc ; zero)

FiniteProductCategory : ∀ 𝑖 -> 𝒰 _
FiniteProductCategory 𝑖 = Category 𝑖 :& hasFiniteProducts


module _ {𝒞 : 𝒰 _} {{_ : FiniteProductCategory 𝑖 on 𝒞}} where
  ⨅-fin : ∀{n} -> (F : Fin n -> 𝒞) -> 𝒞
  ⨅-fin {zero} F = ⊤
  ⨅-fin {suc n} F = F zero ⊓ (⨅-fin (λ i -> F (suc i)))








