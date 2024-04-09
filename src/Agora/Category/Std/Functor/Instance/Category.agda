
module Agora.Category.Std.Functor.Instance.Category where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Natural.Instance.Setoid
open import Agora.Data.Universe.Definition
-- open import Agora.Data.Universe.Instance.Category


module _ (𝒞 : Category 𝑖) (𝒟 : Category 𝑗) where
  macro 𝐅𝐮𝐧𝐜 = #structureOn (Functor 𝒞 𝒟)

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  id-𝐅𝐮𝐧𝐜 : ∀{F : 𝐅𝐮𝐧𝐜 𝒞 𝒟} -> Natural F F
  id-𝐅𝐮𝐧𝐜 {F} = (λ _ -> id) since natural lem-1
    where
      lem-1 : ∀{x y : ⟨ 𝒞 ⟩} (f : x ⟶ y) -> id ◆ map f ∼ map f ◆ id
      lem-1 f = unit-l-◆ ∙ unit-r-◆ ⁻¹

  _◆-𝐅𝐮𝐧𝐜_ : ∀{F G H : 𝐅𝐮𝐧𝐜 𝒞 𝒟} -> Natural F G -> Natural G H -> Natural F H
  _◆-𝐅𝐮𝐧𝐜_ α β = (λ x -> ⟨ α ⟩ x ◆ ⟨ β ⟩ x) since natural lem-1
    where
      lem-1 : ∀{x y : ⟨ 𝒞 ⟩} (f : x ⟶ y) -> (⟨ α ⟩ _ ◆ ⟨ β ⟩ _) ◆ map f ∼ map f ◆ (⟨ α ⟩ _ ◆ ⟨ β ⟩ _)
      lem-1 f = (⟨ α ⟩ _ ◆ ⟨ β ⟩ _) ◆ map f    ⟨ assoc-l-◆ ⟩-∼
                ⟨ α ⟩ _ ◆ (⟨ β ⟩ _ ◆ map f)    ⟨ refl-∼ ◈ naturality f ⟩-∼
                ⟨ α ⟩ _ ◆ (map f ◆ ⟨ β ⟩ _)    ⟨ assoc-r-◆ ⟩-∼
                (⟨ α ⟩ _ ◆ map f) ◆ ⟨ β ⟩ _    ⟨ naturality f ◈ refl-∼ ⟩-∼
                (map f ◆ ⟨ α ⟩ _) ◆ ⟨ β ⟩ _    ⟨ assoc-l-◆ ⟩-∼
                map f ◆ (⟨ α ⟩ _ ◆ ⟨ β ⟩ _)    ∎

  instance
    isCategoryData:Functor : isCategoryData (𝐅𝐮𝐧𝐜 𝒞 𝒟) Natural
    isCategoryData._∼-Hom_ isCategoryData:Functor = _∼-Natural_
    isCategoryData.isEquivRel:∼-Hom isCategoryData:Functor = cast isEquivRel:∼-Natural
    isCategoryData.id isCategoryData:Functor           = id-𝐅𝐮𝐧𝐜
    isCategoryData._◆_ isCategoryData:Functor          = _◆-𝐅𝐮𝐧𝐜_
    isCategoryData.unit-l-◆ isCategoryData:Functor     = incl $ componentwise $ λ _ -> unit-l-◆
    isCategoryData.unit-r-◆ isCategoryData:Functor     = incl $ componentwise $ λ _ -> unit-r-◆
    isCategoryData.unit-2-◆ isCategoryData:Functor     = incl $ componentwise $ λ _ -> unit-2-◆
    isCategoryData.assoc-l-◆ isCategoryData:Functor    = incl $ componentwise $ λ _ -> assoc-l-◆
    isCategoryData.assoc-r-◆ isCategoryData:Functor    = incl $ componentwise $ λ _ -> assoc-r-◆
    isCategoryData._◈_ isCategoryData:Functor          = λ p q -> incl $ componentwise (λ x -> ⟨ ⟨ p ⟩ ⟩ x ◈ ⟨ ⟨ q ⟩ ⟩ x)

    isCategory:Functor : isCategory (𝐅𝐮𝐧𝐜 𝒞 𝒟)
    isCategory:Functor = record { Hom = Natural ; HomData = isCategoryData:Functor }

  {-# OVERLAPS isCategory:Functor #-}
  {-# OVERLAPPABLE isCategoryData:Functor #-}

  instance
    isSetoid:Functor : isSetoid (𝐅𝐮𝐧𝐜 𝒞 𝒟)
    isSetoid:Functor = isSetoid:byCategory



