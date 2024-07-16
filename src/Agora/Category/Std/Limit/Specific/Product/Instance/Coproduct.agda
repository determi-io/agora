-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Limit.Specific.Product.Instance.Coproduct where

open import Agora.Conventions hiding (_⊔_)
open import Agora.Setoid.Definition
-- open import Agora.Data.Fin.Definition
open import Agora.Data.Product.Definition
open import Agora.Data.Sum.Definition
open import Agora.Category.Std.Category.Opposite
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Limit.Specific.Product
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition


module _ {𝒞 : Category 𝑖} where
  module _ {a b : ⟨ 𝒞 ⟩} where
    instance
      isCoproduct:Product : ∀{x} -> {{_ : isProduct a b x}} -> isCoproduct {{of 𝒞 ᵒᵖ}} a b x
      isCoproduct.ι₀ isCoproduct:Product = π₀
      isCoproduct.ι₁ isCoproduct:Product = π₁
      isCoproduct.⦗ isCoproduct:Product ⦘ = ⧼_⧽
      isCoproduct.isSetoidHom:⦗⦘ isCoproduct:Product = it
      isCoproduct.reduce-ι₀ isCoproduct:Product = reduce-π₀
      isCoproduct.reduce-ι₁ isCoproduct:Product = reduce-π₁
      isCoproduct.expand-ι₀,ι₁ isCoproduct:Product = expand-π₀,π₁

  instance
    isInitial:Terminal : ∀{x : ⟨ 𝒞 ⟩} -> {{_ : isTerminal x}} -> isInitial {{of 𝒞 ᵒᵖ}} x
    isInitial.elim-⊥ isInitial:Terminal = intro-⊤
    isInitial.expand-⊥ isInitial:Terminal = expand-⊤


