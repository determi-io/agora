
module Agora.Data.Universe.Instance.hasIndexedCoproducts where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Data.Universe.Definition
open import Agora.Data.Sum.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Definition
-- open import Agora.Category.Std.Category.Construction.Product
open import Agora.Category.Std.Functor.Definition
-- open import Agora.Category.Std.Category.Structured.Monoidal.Definition
-- open import Agora.Algebra.Monoid.Definition
open import Agora.Data.Universe.Instance.Category
-- open import Agora.Category.Std.Natural.Iso
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition
open import Agora.Category.Std.Limit.Specific.Product
-- open import Agora.Category.Std.Category.Structured.FiniteCoproduct.Definition
-- open import Agora.Category.Std.Category.Structured.FiniteProduct.Definition
-- open import Agora.Category.Std.Category.Structured.FiniteProduct.As.Monoid
-- open import Agora.Category.Std.Category.Structured.FiniteCoproduct.As.FiniteProduct


module _ {I : 𝒰 𝑘} {x : I -> 𝒰 𝑘} where

  instance
    isIndexedCoproduct:∑ : isIndexedCoproduct x (∑ x)
    isIndexedCoproduct:∑ = record
      { ιᵢ = λ i x → i , x
      ; ⦗_⦘ᵢ = λ f (i , x) → f i x
      ; reduce-ιᵢ = λ f i → refl-≡
      ; expand-ιᵢ = λ f → refl-≡
      }

instance
  hasIndexedCoproducts:𝐔𝐧𝐢𝐯 : hasIndexedCoproducts (𝐔𝐧𝐢𝐯 𝑖)
  hasIndexedCoproducts:𝐔𝐧𝐢𝐯 = record { ⨆ᵢ = ∑_ }


