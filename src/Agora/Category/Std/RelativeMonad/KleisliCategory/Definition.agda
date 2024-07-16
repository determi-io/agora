-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.RelativeMonad.KleisliCategory.Definition where

open import Agora.Conventions

open import Agora.Setoid
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.RelativeMonad.Definition

-- module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
module _ {C : 𝒰 𝑖} {{_ : isCategory {𝑘} C}} {D : 𝒰 𝑗} {{_ : isCategory {𝑙} D}} where

  private
    𝒞 : Category _
    𝒞 = ′ C ′
    𝒟 : Category _
    𝒟 = ′ D ′

  module _ {J : Functor 𝒞 𝒟}  where
    record RelativeKleisli (T : RelativeMonad J) : 𝒰 𝑖 where
      constructor incl
      field ⟨_⟩ : ⟨ 𝒞 ⟩

    {-# DISPLAY RelativeKleisli.⟨_⟩ a = ⟨ a ⟩ #-}
    open RelativeKleisli {{...}} public


    macro
      𝐑𝐞𝐊𝐥𝐬 : (T : RelativeMonad J) -> SomeStructure
      𝐑𝐞𝐊𝐥𝐬 T = #structureOn (RelativeKleisli T)

  module _ {J : Functor 𝒞 𝒟} {T : RelativeMonad J} where

    record Hom-𝐑𝐞𝐊𝐥𝐬 (a b : 𝐑𝐞𝐊𝐥𝐬 T) : 𝒰 (𝑗 ､ 𝑙) where
      constructor incl
      field ⟨_⟩ : ⟨ J ⟩ ⟨ a ⟩ ⟶ ⟨ T ⟩ ⟨ b ⟩

    {-# DISPLAY Hom-𝐑𝐞𝐊𝐥𝐬.⟨_⟩ a = ⟨ a ⟩ #-}
    open Hom-𝐑𝐞𝐊𝐥𝐬 public

    RelativeKleisliHom : (A B : 𝐑𝐞𝐊𝐥𝐬 T) -> 𝒰 _
    RelativeKleisliHom = Hom-𝐑𝐞𝐊𝐥𝐬

    module _ {A B : 𝐑𝐞𝐊𝐥𝐬 T} where
      record ∼-Hom-𝐑𝐞𝐊𝐥𝐬 (f g : Hom-𝐑𝐞𝐊𝐥𝐬 A B) : 𝒰 (𝑗 ､ 𝑙) where
        constructor incl
        field ⟨_⟩ : ⟨ f ⟩ ∼  ⟨ g ⟩
        -- incl : R a b -> ∼-Hom-𝐑𝐞𝐊𝐥𝐬 R a b -- a ∼[ R ] b
      open ∼-Hom-𝐑𝐞𝐊𝐥𝐬 public

      _∼-RelativeKleisliHom_ : (f g : RelativeKleisliHom A B) -> 𝒰 _
      _∼-RelativeKleisliHom_ = ∼-Hom-𝐑𝐞𝐊𝐥𝐬
      -- (λ f g -> ⟨ f ⟩ ∼ ⟨ g ⟩)


      instance
        isSetoid:RelativeKleisliHom : isSetoid (RelativeKleisliHom A B)
        isSetoid._∼_ isSetoid:RelativeKleisliHom = _∼-RelativeKleisliHom_
        isSetoid.refl isSetoid:RelativeKleisliHom {a} = incl refl
        isSetoid.sym isSetoid:RelativeKleisliHom {a} {b} p = incl (sym ⟨ p ⟩)
        isSetoid._∙_ isSetoid:RelativeKleisliHom {a} p q = incl $ ⟨ p ⟩ ∙ ⟨ q ⟩

    id-𝐑𝐞𝐊𝐥𝐬 : ∀{a : 𝐑𝐞𝐊𝐥𝐬 T} -> RelativeKleisliHom a a
    id-𝐑𝐞𝐊𝐥𝐬 = incl repure

    infixl 50 _◆-𝐑𝐞𝐊𝐥𝐬_
    _◆-𝐑𝐞𝐊𝐥𝐬_ : ∀{a b c : 𝐑𝐞𝐊𝐥𝐬 T} -> (RelativeKleisliHom a b) -> (RelativeKleisliHom b c) -> RelativeKleisliHom a c
    _◆-𝐑𝐞𝐊𝐥𝐬_ f g = incl (⟨ f ⟩ ◆ reext ⟨ g ⟩)

    private
      lem-1 : ∀{a b : 𝐑𝐞𝐊𝐥𝐬 T} -> {f : RelativeKleisliHom a b} -> id-𝐑𝐞𝐊𝐥𝐬 ◆-𝐑𝐞𝐊𝐥𝐬 f ∼ f
      lem-1 = incl reunit-l

      lem-2 : ∀{a b : 𝐑𝐞𝐊𝐥𝐬 T} -> {f : RelativeKleisliHom a b} -> f ◆-𝐑𝐞𝐊𝐥𝐬 id-𝐑𝐞𝐊𝐥𝐬 ∼ f
      lem-2 = incl ((refl ◈ reunit-r) ∙ unit-r-◆)

      lem-3 : ∀{a b c d : 𝐑𝐞𝐊𝐥𝐬 T} {f : RelativeKleisliHom a b} {g : RelativeKleisliHom b c} {h : RelativeKleisliHom c d}
              -> (f ◆-𝐑𝐞𝐊𝐥𝐬 g) ◆-𝐑𝐞𝐊𝐥𝐬 h ∼ f ◆-𝐑𝐞𝐊𝐥𝐬 (g ◆-𝐑𝐞𝐊𝐥𝐬 h)
      lem-3 {f = incl f} {incl g} {incl h} = incl P
        where
          P : (f ◆ reext g) ◆ reext h ∼ f ◆ (reext (g ◆ reext h))
          P = (f ◆ reext g) ◆ reext h   ⟨ assoc-l-◆ ⟩-∼
              f ◆ (reext g ◆ reext h)   ⟨ refl ◈ reassoc ⟩-∼
              f ◆ (reext (g ◆ reext h)) ∎

    instance
      isCategory:RelativeKleisli : isCategory (RelativeKleisli T)
      isCategory.Hom isCategory:RelativeKleisli A B = RelativeKleisliHom A B
      isCategory.isSetoid:Hom isCategory:RelativeKleisli = it
      isCategory.id isCategory:RelativeKleisli         = incl repure
      isCategory._◆_ isCategory:RelativeKleisli        = _◆-𝐑𝐞𝐊𝐥𝐬_
      isCategory.unit-l-◆ isCategory:RelativeKleisli   = lem-1
      isCategory.unit-r-◆ isCategory:RelativeKleisli   = lem-2
      isCategory.unit-2-◆ isCategory:RelativeKleisli   = lem-1
      isCategory.assoc-l-◆ isCategory:RelativeKleisli  = lem-3
      isCategory.assoc-r-◆ isCategory:RelativeKleisli  = (lem-3 ⁻¹)
      isCategory._◈_ isCategory:RelativeKleisli        = {!!} -- λ p q -> incl $ lem-4 ⟨ p ⟩ ⟨ q ⟩


    --------------------------------------------------------------
    -- The functor from the category 𝒞 to 𝐑𝐞𝐊𝐥𝐬 T
    --
    -- Note: There is a functor |ι : 𝒞 → 𝐑𝐞𝐊𝐥𝐬 T|,
    --       but there is no |♮ : 𝐑𝐞𝐊𝐥𝐬 T → 𝒞|,
    --       because even though the objects of |𝐑𝐞𝐊𝐥𝐬 T|
    --       are from |𝒞|, the morphisms lie in |𝒟|,
    --       so we cannot build that functor.
    --

    ι-𝐑𝐞𝐊𝐥𝐬ᵘ : C -> 𝐑𝐞𝐊𝐥𝐬 T
    ι-𝐑𝐞𝐊𝐥𝐬ᵘ x = incl x

    macro ι-𝐑𝐞𝐊𝐥𝐬 = #structureOn ι-𝐑𝐞𝐊𝐥𝐬ᵘ

    map-ι-𝐑𝐞𝐊𝐥𝐬 : ∀{a b : C} -> (a ⟶ b) -> ι-𝐑𝐞𝐊𝐥𝐬 a ⟶ ι-𝐑𝐞𝐊𝐥𝐬 b
    map-ι-𝐑𝐞𝐊𝐥𝐬 f = incl (map f ◆ repure)

    instance
      isFunctor:ι-𝐑𝐞𝐊𝐥𝐬 : isFunctor 𝒞 (𝐑𝐞𝐊𝐥𝐬 T) ι-𝐑𝐞𝐊𝐥𝐬
      isFunctor.map isFunctor:ι-𝐑𝐞𝐊𝐥𝐬 = map-ι-𝐑𝐞𝐊𝐥𝐬
      isFunctor.isSetoidHom:map isFunctor:ι-𝐑𝐞𝐊𝐥𝐬 = {!!}
      isFunctor.functoriality-id isFunctor:ι-𝐑𝐞𝐊𝐥𝐬 = {!!}
      isFunctor.functoriality-◆ isFunctor:ι-𝐑𝐞𝐊𝐥𝐬 = {!!}

    open import Agora.Category.Std.Functor.EssentiallySurjective
    instance
      isEssentiallySurjective:ι-𝐑𝐞𝐊𝐥𝐬 : isEssentiallySurjective ι-𝐑𝐞𝐊𝐥𝐬
      isEssentiallySurjective:ι-𝐑𝐞𝐊𝐥𝐬 = essentiallysurjective (λ x -> ⟨ x ⟩) refl-≅


