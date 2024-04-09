
module Agora.Category.Std.Category.Construction.Product where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Data.Product.Definition
open import Agora.Data.Lift.Definition
-- open import Agora.Data.Fin.Definition
-- open import Agora.Algebra.Monoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Instance.CategoryLike
open import Agora.Category.Std.Category.Construction.Id
open import Agora.Category.Std.Limit.Specific.Product
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Constant
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Natural.Instance.Setoid
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Morphism.Iso


--------------------------------------------------------------
-- Showing that _×_ on universes lifts to categories

module _ {𝒞 : 𝒰 𝑖} {𝒟 : 𝒰 𝑗} {{𝒞p : isCategory {𝑖₁} 𝒞}} {{𝒟p : isCategory {𝑗₁} 𝒟}} where

  Hom-×-𝐂𝐚𝐭 : (x y : 𝒞 × 𝒟) -> 𝒰 _
  Hom-×-𝐂𝐚𝐭 = λ (a , b) (c , d) -> (a ⟶ c) × (b ⟶ d)
  -- isCategory.Hom isCategory:× = λ (a , b) (c , d) -> (a ⟶ c) × (b ⟶ d)

  instance
    isCategoryData:× : isCategoryData (𝒞 × 𝒟) Hom-×-𝐂𝐚𝐭
    isCategoryData.isSetoid:Hom isCategoryData:× = isSetoid:× {{isCategoryData:isSetoid2 {{HomData (𝒞p)}}}} {{isCategoryData:isSetoid2 {{HomData (𝒟p)}}}}
    isCategoryData.id isCategoryData:×         = id , id
    isCategoryData._◆_ isCategoryData:×        = λ (f₀ , g₀) (f₁ , g₁) -> (f₀ ◆ f₁ , g₀ ◆ g₁)
    isCategoryData.unit-l-◆ isCategoryData:×   = incl $ unit-l-◆ , unit-l-◆
    isCategoryData.unit-r-◆ isCategoryData:×   = incl $ unit-r-◆ , unit-r-◆
    isCategoryData.unit-2-◆ isCategoryData:×   = incl $ unit-2-◆ , unit-2-◆
    isCategoryData.assoc-l-◆ isCategoryData:×  = incl $ assoc-l-◆ , assoc-l-◆
    isCategoryData.assoc-r-◆ isCategoryData:×  = incl $ assoc-r-◆ , assoc-r-◆
    isCategoryData._◈_ isCategoryData:×        = λ (incl (p₀ , q₀)) (incl (p₁ , q₁)) -> incl (p₀ ◈ p₁ , q₀ ◈ q₁)

{-

    isCategory:× : isCategory (𝒞 × 𝒟)
    isCategory.Hom isCategory:× = λ (a , b) (c , d) -> (a ⟶ c) × (b ⟶ d)


  -- currently special treatment for isomorphisms
  into-×-≅ : ∀{a b : 𝒞} {c d : 𝒟} -> (p : a ≅ b) (q : c ≅ d) -> (a , c) ≅ (b , d)
  into-×-≅ p q = (⟨ p ⟩ , ⟨ q ⟩) since P
    where
      P = record
          { inverse-◆  = (inverse-◆ (of p) , inverse-◆ (of q))
          ; inv-r-◆    = incl $ inv-r-◆ (of p) , inv-r-◆ (of q)
          ; inv-l-◆    = incl $ inv-l-◆ (of p) , inv-l-◆ (of q)
          }

_×-𝐂𝐚𝐭_ :(𝒞 : Category 𝑖) (𝒟 : Category 𝑗) -> Category _
_×-𝐂𝐚𝐭_ 𝒞 𝒟 = 𝒞 × 𝒟

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  π₀-𝐂𝐚𝐭 : Functor (𝒞 × 𝒟) 𝒞
  π₀-𝐂𝐚𝐭 = fst since P
    where
      P : isFunctor _ _ fst
      isFunctor.map P              = fst
      isFunctor.isSetoidHom:map P  = record { cong-∼ = fst }
      isFunctor.functoriality-id P = refl-∼
      isFunctor.functoriality-◆ P  = refl-∼

  π₁-𝐂𝐚𝐭 : Functor (𝒞 × 𝒟) 𝒟
  π₁-𝐂𝐚𝐭 = snd since P
    where
      P : isFunctor _ _ snd
      isFunctor.map P              = snd
      isFunctor.isSetoidHom:map P  = record { cong-∼ = snd }
      isFunctor.functoriality-id P = refl-∼
      isFunctor.functoriality-◆ P  = refl-∼

module _ {𝒳 : Category 𝑖} {𝒞 : Category 𝑗} {𝒟 : Category 𝑘} where
  ⧼_⧽-𝐂𝐚𝐭 : (Functor 𝒳 𝒞) × (Functor 𝒳 𝒟) -> Functor 𝒳 (𝒞 × 𝒟)
  ⧼_⧽-𝐂𝐚𝐭 (F , G) = h since P
    where
      h : ⟨ 𝒳 ⟩ -> 𝒞 × 𝒟
      h x = ⟨ F ⟩ x , ⟨ G ⟩ x

      P : isFunctor _ _ h
      isFunctor.map P              = λ ϕ -> map ϕ , map ϕ
      isFunctor.isSetoidHom:map P  = record { cong-∼ = λ p -> cong-∼ p , cong-∼ p }
      isFunctor.functoriality-id P = functoriality-id , functoriality-id
      isFunctor.functoriality-◆ P  = functoriality-◆ , functoriality-◆

  module _ {F : Functor 𝒳 𝒞} {G : Functor 𝒳 𝒟} where
    reduce-π₀-𝐂𝐚𝐭 : (⧼ F , G ⧽-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭) ≅ F
    reduce-π₀-𝐂𝐚𝐭 = α since P
      where
        α : Natural (⧼ F , G ⧽-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭) F
        α = (λ _ -> id) since natural (naturality {{of id-𝐅𝐮𝐧𝐜 {F = F}}})

        β : Natural F (⧼ F , G ⧽-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭)
        β = (λ _ -> id) since natural (naturality {{of id-𝐅𝐮𝐧𝐜 {F = F}}})

        P : isIso (hom α)
        P = record
            { inverse-◆  = β
            ; inv-r-◆    = componentwise $ λ _ -> unit-2-◆
            ; inv-l-◆    = componentwise $ λ _ -> unit-2-◆
            }

    reduce-π₁-𝐂𝐚𝐭 : (⧼ F , G ⧽-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭) ≅ G
    reduce-π₁-𝐂𝐚𝐭 = α since P
      where
        α : Natural (⧼ F , G ⧽-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭) G
        α = (λ _ -> id) since natural (naturality {{of id-𝐅𝐮𝐧𝐜 {F = G}}})

        β : Natural G (⧼ F , G ⧽-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭)
        β = (λ _ -> id) since natural (naturality {{of id-𝐅𝐮𝐧𝐜 {F = G}}})

        P : isIso (hom α)
        P = record
            { inverse-◆  = β
            ; inv-r-◆    = componentwise $ λ _ -> unit-2-◆
            ; inv-l-◆    = componentwise $ λ _ -> unit-2-◆
            }

  module _ {F : Functor 𝒳 (𝒞 × 𝒟)} where
    expand-⊓-𝐂𝐚𝐭 : F ≅ ⧼ F ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭 , F ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭 ⧽-𝐂𝐚𝐭
    expand-⊓-𝐂𝐚𝐭 = α since P
      where
        α : Natural F ⧼ F ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭 , F ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭 ⧽-𝐂𝐚𝐭
        α = (λ _ -> id , id) since natural (λ f → unit-l-◆ ∙ unit-r-◆ ⁻¹ , unit-l-◆ ∙ unit-r-◆ ⁻¹)

        β : Natural ⧼ F ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭 , F ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭 ⧽-𝐂𝐚𝐭 F
        β = (λ _ -> id , id) since natural (λ f → unit-l-◆ ∙ unit-r-◆ ⁻¹ , unit-l-◆ ∙ unit-r-◆ ⁻¹)

        P : isIso (hom α)
        P = record
            { inverse-◆  = β
            ; inv-r-◆    = componentwise $ λ _ -> unit-2-◆ , unit-2-◆
            ; inv-l-◆    = componentwise $ λ _ -> unit-2-◆ , unit-2-◆
            }


--------------------------------------------------------------
-- The 0-ary product, 𝟙

isSet:⊤-𝒰 : ∀{a b : ⊤-𝒰} {p q : a ≡ b} -> p ≡ q
isSet:⊤-𝒰 = ?

instance
  isCategory:𝟙 : isCategory (⊤-𝒰 {𝑖})
  isCategory:𝟙 = isCategory:byId

⊤-𝐂𝐚𝐭 : Category 𝑖
⊤-𝐂𝐚𝐭 = ′(Lift-Cat (𝟙 {ℓ₀}))′

intro-⊤-𝐂𝐚𝐭 : ∀{𝒞 : 𝐂𝐚𝐭 𝑖} -> Functor 𝒞 (⊤-𝐂𝐚𝐭 {𝑗})
intro-⊤-𝐂𝐚𝐭 = const (lift tt) since isFunctor:const

expand-⊤-𝐂𝐚𝐭 : ∀{𝒞 : 𝐂𝐚𝐭 𝑖} -> {F : Functor 𝒞 (⊤-𝐂𝐚𝐭 {𝑗})} -> F ≅ intro-⊤-𝐂𝐚𝐭
expand-⊤-𝐂𝐚𝐭 {F = F} = α since P
  where
    α : Natural F intro-⊤-𝐂𝐚𝐭
    α = (λ _ -> incl isProp:⊤-𝒰) since natural (λ _ → ↥ isSet:⊤-𝒰)

    β : Natural intro-⊤-𝐂𝐚𝐭 F
    β = (λ _ -> incl isProp:⊤-𝒰) since natural (λ _ → ↥ isSet:⊤-𝒰)

    P : isIso (hom α)
    P = record
        { inverse-◆ = β
        ; inv-r-◆   = componentwise $ λ _ -> ↥ isSet:⊤-𝒰
        ; inv-l-◆   = componentwise $ λ _ -> ↥ isSet:⊤-𝒰
        }





-}

