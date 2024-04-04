
module Agora.Category.Std.Fibration.GrothendieckConstruction.Op.Instance.FiniteCoproductCategory where

open import Agora.Conventions hiding (_⊔_)

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Opposite
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Limit.Specific.Coproduct.Definition
open import Agora.Category.Std.Limit.Specific.Product

open import Agora.Category.Std.Fibration.GrothendieckConstruction.Op.Definition


-- record hasCoproductGluing (F : Functor 𝒞 ᵒᵖ)

-- module _ {𝒞 : Category 𝑖} {F : Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)}
--          {{_ : hasCoproducts 𝒞}}
--          -- {{_ : ∀{c : ⟨ 𝒞 ⟩} -> hasCoproducts (⟨ F ⟩ c)}}
--   where

--   infixl 80 _⊔-⨊ᵒᵖ_

--   _⊔-⨊ᵒᵖ_ : ⨊ᵒᵖ F -> ⨊ᵒᵖ F -> ⨊ᵒᵖ F
--   _⊔-⨊ᵒᵖ_ a b = (base a ⊔ base b) , {!!}
--   -- ⟨ map π₀ ⟩ (fib a) ⊔ ⟨ map π₁ ⟩ (fib b)

--   -- module _ {a b : ⨊ᵒᵖ F} where
--   --   ι₀-⨊ᵒᵖ : a ⟶ a ⊔-⨊ᵒᵖ b
--   --   ι₀-⨊ᵒᵖ = {!!} , {!!}
--   instance
--     hasCoproducts:⨊ᵒᵖ : hasCoproducts ′(⨊ᵒᵖ F)′
--     hasCoproducts:⨊ᵒᵖ = {!!}

--   instance
--     hasFiniteCoproducts:⨊ᵒᵖ : hasFiniteCoproducts ′(⨊ᵒᵖ F)′
--     hasFiniteCoproducts:⨊ᵒᵖ = {!!}



