
{-# OPTIONS --allow-unsolved-metas #-}

module Agora.Category.Std.Limit.Specific.Product.Instance.Functor where

open import Agora.Conventions
open import Agora.Setoid.Definition
-- open import Agora.Data.Fin.Definition
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Category.Construction.Product
open import Agora.Category.Std.Limit.Specific.Product
open import Agora.Category.Std.Category.Structured.FiniteProduct.Definition

module _ {𝒞 : 𝒰 _} {{_ : FiniteProductCategory 𝑖 on 𝒞}} where

  private
    𝒞' : Category 𝑖
    𝒞' = ′ 𝒞 ′

  map-⊓ : ∀{a b c d : 𝒞} -> (a ⟶ b) × (c ⟶ d) -> (a ⊓ c ⟶ b ⊓ d)
  map-⊓ (f , g) = ⧼ π₀ ◆ f , π₁ ◆ g ⧽

  infixl 100 _⇃⊓⇂_
  _⇃⊓⇂_ : ∀{a b c d : 𝒞} -> (a ⟶ b) -> (c ⟶ d) -> (a ⊓ c ⟶ b ⊓ d)
  _⇃⊓⇂_ = λ₊ map-⊓


  private instance
    -- TODO: Why is it necessary to create this local instance?
    _ = isSetoidHom:⧼⧽

  private
    lem-1 : ∀{a b : 𝒞} -> map-⊓ (id {a = a} , id {a = b}) ∼ id
    lem-1 {a} {b} = P
      where
        ida : a ⟶ a
        ida = id

        idb : b ⟶ b
        idb = id

        idab : (a ⊓ b) ⟶ (a ⊓ b)
        idab = id

        P = ⧼ π₀ ◆ ida , π₁ ◆ idb ⧽    ⟨ cong-∼ (unit-r-◆ ∙ unit-l-◆ ⁻¹ , unit-r-◆ ∙ unit-l-◆ ⁻¹) ⟩-∼
            ⧼ idab ◆ π₀ , idab ◆ π₁ ⧽  ⟨ expand-π₀,π₁ ⁻¹ ⟩-∼
            idab                       ∎

  isFunctor:⊓ : isFunctor (𝒞' ×-𝐂𝐚𝐭 𝒞') 𝒞' ⊓⃨
  isFunctor.map isFunctor:⊓               = map-⊓
  isFunctor.isSetoidHom:map isFunctor:⊓   = record { cong-∼ = λ (incl (p , q)) → cong-∼ (refl-∼ ◈ p , refl-∼ ◈ q) }
  isFunctor.functoriality-id isFunctor:⊓  = lem-1
  isFunctor.functoriality-◆ isFunctor:⊓   = {!!}



