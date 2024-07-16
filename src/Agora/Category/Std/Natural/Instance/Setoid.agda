-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Natural.Instance.Setoid where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {F G : Functor 𝒞 𝒟} where

  record _∼-Natural_ (α β : Natural F G) : 𝒰 (𝑖 ､ 𝑗) where
    constructor componentwise
    field ⟨_⟩ : ∀(x : ⟨ 𝒞 ⟩) -> ⟨ α ⟩ x ∼ ⟨ β ⟩ x

  open _∼-Natural_ public


  -- _∼-Natural_ : (α β : Natural F G) -> 𝒰 _
  -- α ∼-Natural β = ∀(x : ⟨ 𝒞 ⟩) -> ⟨ α ⟩ x ∼ ⟨ β ⟩ x

  -- instance
  --   isEquivRel:∼-Natural : isEquivRel (∼-Base (λ (a b : Hom-Base Natural F G) -> ⟨ a ⟩ ∼-Natural ⟨ b ⟩))
    -- isEquivRel.refl isEquivRel:∼-Natural = incl refl
    -- isEquivRel.sym isEquivRel:∼-Natural (incl p) = incl (sym p)
    -- isEquivRel._∙_ isEquivRel:∼-Natural (incl p) (incl q) = incl (p ∙ q)

  instance
    isEquivRel:∼-Natural : isEquivRel _∼-Natural_
    isEquivRel:∼-Natural = record
      { refl-∼ = (componentwise (λ _ -> refl-∼))
      ; sym = λ p -> componentwise λ x -> sym (⟨ p ⟩ x)
      ; _∙_ = λ p q -> componentwise λ x -> ⟨ p ⟩ x ∙ ⟨ q ⟩ x
      }

    isSetoid:Natural : isSetoid (Natural F G)
    isSetoid:Natural = record { _∼_ = _∼-Natural_ } 
    -- isSetoid:byDef _∼-Natural_ (componentwise (λ _ -> refl)) {!!} {!!}
    -- isSetoid._∼'_ isSetoid:Natural a b = ⟨ a ⟩ ∼-Natural ⟨ b ⟩
    -- isSetoid.isEquivRel:∼ isSetoid:Natural = isEquivRel:∼-Natural


