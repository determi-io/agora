
module Agora.Data.Lift.Definition where

open import Agora.Conventions
open import Agora.Category.Std.Category.Definition
-- open import Agora.Algebra.Monoid.Definition

record Lift-Cat {j : 𝔏 ^ 3} {i} (A : 𝒰 i) : 𝒰 (i ⊔ (j ⌄ 0)) where
  constructor lift
  field
    lower : A
open Lift-Cat public




record Hom-Lift 𝑘 {𝑖 𝑗 : 𝔏} {A : 𝒰 𝑖} (Hom : A -> A -> 𝒰 𝑗) (a : Lift-Cat {𝑘} A) (b : Lift-Cat {𝑘} A) : 𝒰 (𝑗 ⊔ (𝑘 ⌄ 1)) where
  constructor incl
  field ⟨_⟩ : Hom (lower a) (lower b)
  -- incl : R a b -> Hom-Base R a b -- a ∼[ R ] b
open Hom-Lift public




module _ {𝒞 : 𝒰 𝑖} {{𝒞p : isCategory {𝑗} 𝒞}} where

  module _ {𝑘} {a : Lift-Cat {𝑘} 𝒞} {b : Lift-Cat {𝑘} 𝒞} where
    record _∼-Hom-Lift_ (f g : Hom-Lift 𝑘 (Hom {{𝒞p}}) a b) : 𝒰 (𝑗 ⌄ 1 ⊔ (𝑘 ⌄ 2)) where
      constructor incl
      field ⟨_⟩ : ⟨ f ⟩ ∼ ⟨ g ⟩

    open _∼-Hom-Lift_ public
  -- _∼-Hom-Lift_ = (λ f g -> ⟨ f ⟩ ∼ ⟨ g ⟩)

  -- instance
  --   isEquivRel:Hom-Lift : isEquivRel (_∼-Hom-Lift_)
  --   isEquivRel:Hom-Lift = isEquivRel:HomRel {{record { refl-∼ = refl-∼ ; sym = sym ; _∙_ = _∙_ }}}

    isEquivRel:∼-Hom-Lift : isEquivRel _∼-Hom-Lift_
    isEquivRel:∼-Hom-Lift = record { refl-∼ = incl refl-∼ ; sym = λ p -> incl (sym ⟨ p ⟩) ; _∙_ = λ (incl p) (incl q) -> incl (p ∙ q) }

    isSetoid:Hom-Lift : isSetoid (Hom-Lift 𝑘 (Hom {{𝒞p}}) a b)
    isSetoid:Hom-Lift = record {_∼_ = _ ; isEquivRel:∼ = isEquivRel:∼-Hom-Lift}

  instance
    isCategoryData:Lift : ∀{𝑘} -> isCategoryData (Lift-Cat {𝑘} 𝒞) (Hom-Lift 𝑘 (Hom {{𝒞p}}))
    isCategoryData.isSetoid:Hom (isCategoryData:Lift {𝑘}) = isSetoid:Hom-Lift
    isCategoryData.id (isCategoryData:Lift {𝑘}) = incl id
    isCategoryData._◆_ (isCategoryData:Lift {𝑘}) f g = incl (⟨ f ⟩ ◆ ⟨ g ⟩)
    isCategoryData.unit-l-◆ (isCategoryData:Lift {𝑘})  = incl $ incl $ unit-l-◆ -- {{𝒞p}}
    isCategoryData.unit-r-◆ (isCategoryData:Lift {𝑘})  = incl $ incl $ unit-r-◆ -- {{𝒞p}}
    isCategoryData.unit-2-◆ (isCategoryData:Lift {𝑘})  = incl $ incl $ unit-2-◆ -- {{𝒞p}}
    isCategoryData.assoc-l-◆ (isCategoryData:Lift {𝑘}) = incl $ incl $ assoc-l-◆ -- {{𝒞p}}
    isCategoryData.assoc-r-◆ (isCategoryData:Lift {𝑘}) = incl $ incl $ assoc-r-◆ -- {{𝒞p}}
    isCategoryData._◈_ (isCategoryData:Lift {𝑘}) = λ p q -> incl $ incl $ ⟨ ⟨ p ⟩ ⟩ ◈ ⟨ ⟨ q ⟩ ⟩

    isCategory:Lift : ∀{𝑘} -> isCategory (Lift-Cat {𝑘} 𝒞)
    isCategory:Lift {𝑘} = record { Hom = Hom-Lift 𝑘 (Hom {{𝒞p}}) ; HomData = isCategoryData:Lift {𝑘} }

  {-# INCOHERENT isCategory:Lift #-}
  -- {-# OVERLAPS isCategory:Lift #-}
  -- {-# OVERLAPS isCategoryData:Lift #-}




