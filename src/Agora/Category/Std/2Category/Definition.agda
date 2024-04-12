
module Agora.Category.Std.2Category.Definition where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
-- open import Agora.Category.Std.Category.Instance.Category
-- open import Agora.Category.Std.Category.Instance.FiniteProductCategory
open import Agora.Category.Std.Category.Construction.Product
open import Agora.Category.Std.Functor.Definition
-- open import Agora.Category.Std.Functor.Constant
-- open import Agora.Category.Std.Functor.Instance.Category
-- open import Agora.Category.Std.Natural.Definition
-- open import Agora.Category.Std.Natural.Instance.Setoid
-- open import Agora.Category.Std.Limit.Specific.Product
-- open import Agora.Setoid.As.Category
-- open import Agora.Category.Std.Groupoid.As.Setoid
open import Agora.Category.Std.Morphism.Iso
-- open import Agora.Category.Std.Groupoid.Definition
-- open import Agora.Category.Std.Category.Construction.Core
-- open import Agora.Setoid.Instance.Category




record is2Category {𝑗 : 𝔏 ^ 2} {𝑖} (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field 2Hom : ∀{a b : ⟨ 𝒞 ⟩} -> (f g : a ⟶ b) -> 𝒰 (𝑗 ⌄ 0)
  field {{2HomData}} : ∀{a b : ⟨ 𝒞 ⟩} -> isCategoryData {𝑗 = 𝑗} (a ⟶ b) 2Hom

  private instance
    isCategory:2Hom : ∀{a b : ⟨ 𝒞 ⟩} -> isCategory (a ⟶ b)
    isCategory:2Hom = record { Hom = 2Hom ; HomData = 2HomData }

  Comp : ∀{a b c : ⟨ 𝒞 ⟩} -> ((a ⟶ b) × (b ⟶ c)) -> (a ⟶ c)
  Comp = λ (f , g) -> f ◆ g

  Id : ∀{a : ⟨ 𝒞 ⟩} -> ⟨ ⊤-𝐂𝐚𝐭 {𝑖 ⌄ 0 , 𝑗 ⌄ 0 ⋯ 1} ⟩ -> a ⟶ a
  Id = λ _ -> id

  field {{isFunctor:Comp}} : ∀{a b c : ⟨ 𝒞 ⟩} -> isFunctor ((a ⟶ b) ×-𝐂𝐚𝐭 (b ⟶ c)) (a ⟶ c) Comp
  field {{isFunctor:Id}} : ∀{a : ⟨ 𝒞 ⟩} -> isFunctor ⊤-𝐂𝐚𝐭 (a ⟶ a) Id

  -- we can interpret the setoid on arrows as isos in the category of 2cells
  field 2celliso : ∀{a b : ⟨ 𝒞 ⟩} -> {f g : a ⟶ b} -> f ∼ g -> f ≅ g

open is2Category ⦃...⦄ public

module _ (𝑖 : 𝔏 ^ 5) where
  2Category = Category (𝑖 ⌄ 0 ⋯ 2) :& is2Category {𝑖 ⌄ 3 ⋯ 4}


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} {{_ : is2Category {𝑘} ′ 𝒞 ′}} {a b : 𝒞} (f g : a ⟶ b) where
  infixr 40 _⟹ᵘ_ _⟹_
  _⟹ᵘ_ = 2Hom f g
  macro _⟹_ = #structureOn (2Hom f g)

-- module _ {𝒞 : 𝒰 _} {{_ : 2Category 𝑖 on 𝒞}} where
module _ {𝒞 : 𝒰 𝑖} {{𝒞P : isCategory {𝑗} 𝒞}} {{𝒞P2 : is2Category {𝑘} ′ 𝒞 ′}} where
  _⇃◆⇂_ : ∀{a b c : 𝒞} -> {f g : a ⟶ b} -> {h i : b ⟶ c}
          -> f ⟹ g -> h ⟹ i -> f ◆ h ⟹ g ◆ i
  _⇃◆⇂_ α β = map (α , β)
  infixl 50 _⇃◆⇂_


module _ {𝒞 : 𝒰 𝑖} {{𝒞P : isCategory {𝑗} 𝒞}} {{𝒞P2 : is2Category {𝑘} ′ 𝒞 ′}} where

  -- the directed counterparts of the unitality and associativity laws
  υ-l-◆ : ∀{a b : 𝒞} {f : a ⟶ b} -> (id ◆ f) ⟹ f
  υ-l-◆ = ⟨ 2celliso unit-l-◆ ⟩

  υ-r-◆ : ∀{a b : 𝒞} {f : a ⟶ b} -> (f ◆ id) ⟹ f
  υ-r-◆ = ⟨ 2celliso unit-r-◆ ⟩

  α-l-◆ : ∀{a b c d : 𝒞} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
        -> (f ◆ g) ◆ h ⟹ f ◆ (g ◆ h)
  α-l-◆ = ⟨ 2celliso assoc-l-◆ ⟩

  α-r-◆ : ∀{a b c d : 𝒞} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
        -> f ◆ (g ◆ h) ⟹ (f ◆ g) ◆ h
  α-r-◆ = ⟨ 2celliso assoc-r-◆ ⟩


{-
  interchange-⇃◆⇂ : ∀{a b c : 𝒞} -> {f₀ g₀ h₀ : a ⟶ b} -> {f₁ g₁ h₁ : b ⟶ c}
          -> (α₀ : f₀ ⟹ g₀) -> (β₀ : g₀ ⟹ h₀)
          -> (α₁ : f₁ ⟹ g₁) -> (β₁ : g₁ ⟹ h₁)
          -> (α₀ ◆ β₀) ⇃◆⇂ (α₁ ◆ β₁) ∼ (α₀ ⇃◆⇂ α₁) ◆ (β₀ ⇃◆⇂ β₁)
  interchange-⇃◆⇂ = {!!}
  -}


