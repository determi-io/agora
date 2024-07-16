-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Natural.Iso where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Natural.Instance.Setoid
open import Agora.Data.Universe.Instance.Setoid




module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isNaturalIso (F G : Functor 𝒞 𝒟) (α : ∀{x : ⟨ 𝒞 ⟩} -> (⟨ F ⟩ x) ≅ (⟨ G ⟩ x)) : 𝒰 (𝑖 ､ 𝑗) where
    constructor naturalIso'
    field {{fstNaturalIso}} : isNatural F G (λ x -> ⟨ α {x} ⟩)
    field {{sndNaturalIso}}  : isNatural G F (λ x -> inverse-◆ (of (α {x})))

  open isNaturalIso {{...}} public

  pattern naturalIso a b = naturalIso' {{natural a}} {{natural b}}

  module _ (F G : Functor 𝒞 𝒟) where
    NaturalIso = _ :& isNaturalIso F G

  module _ {F G : Functor 𝒞 𝒟} where

    Iso≅NaturalIso : (F ≅ G) ≅-𝒰 NaturalIso F G
    Iso≅NaturalIso = ϕ since {!!}
      where
        -- we change the iso α to the the family of isos αs
        ϕ : (F ≅ G) -> NaturalIso F G
        ϕ α = αs since naturalIso (naturality {{of ⟨ α ⟩}}) ((naturality {{of ⟨ α ⟩⁻¹}}))
          where
            αs₀ : ∀{x : ⟨ 𝒞 ⟩} -> ⟨ F ⟩ x ⟶ ⟨ G ⟩ x
            αs₀ {x} = ⟨ ⟨ α ⟩ ⟩ x

            αs₁ : ∀{x : ⟨ 𝒞 ⟩} -> ⟨ G ⟩ x ⟶ ⟨ F ⟩ x
            αs₁ {x} = ⟨ ⟨ α ⟩⁻¹ ⟩ x

            lem₀ : ∀{x} -> αs₀ {x} ◆ αs₁ {x} ∼ id
            lem₀ = let P = inv-r-◆ (of α) in ⟨ P ⟩ _

            lem₁ : ∀{x} -> αs₁ {x} ◆ αs₀ {x} ∼ id
            lem₁ = let P = inv-l-◆ (of α) in ⟨ P ⟩ _

            αs : ∀{x : ⟨ 𝒞 ⟩} -> ⟨ F ⟩ x ≅ ⟨ G ⟩ x
            αs = αs₀ since record { inverse-◆ = αs₁ ; inv-r-◆ = lem₀ ; inv-l-◆ = lem₁ }

    instance
      -- _ = introBicoercible Iso≅NaturalIso
      _ = introCoercible Iso≅NaturalIso




