
module Agora.Category.Std.2Category.Definition where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Data.AllOf.Product
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
-- open import Agora.Category.Std.Morphism.Iso
-- open import Agora.Category.Std.Groupoid.Definition
-- open import Agora.Category.Std.Category.Construction.Core
-- open import Agora.Setoid.Instance.Category



record is2Category {𝑗 : 𝔏 ^ 2} {𝑖} (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field cell : ∀(a b : ⟨ 𝒞 ⟩) -> isCategory {𝑗} (a ⟶ b)

  Cell : ∀(a b : ⟨ 𝒞 ⟩) -> Category _
  Cell a b = a ⟶ᵘ b since cell a b

  Comp : ∀{a b c} -> (Cell a b × Cell b c) -> (a ⟶ c)
  Comp = λ (f , g) -> f ◆ g

  Id : ∀{a : ⟨ 𝒞 ⟩} -> ⟨ ⊤-𝐂𝐚𝐭 {𝑖 ⌄ 0 , 𝑗 ⌄ 0 ⋯ 1} ⟩ -> a ⟶ a
  Id = λ _ -> id

  field isFunctor:Comp : ∀{a b c} -> isFunctor (Cell a b ×-𝐂𝐚𝐭 Cell b c) (Cell a c) Comp
  field isFunctor:Id : ∀{a} -> isFunctor ⊤-𝐂𝐚𝐭 (Cell a a) Id


module _ (𝑖 : 𝔏 ^ 5) where
  2Category = Category (𝑖 ⌄ 0 ⋯ 2) :& is2Category {𝑖 ⌄ 3 ⋯ 4}



