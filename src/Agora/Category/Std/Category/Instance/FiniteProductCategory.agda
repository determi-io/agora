
module Agora.Category.Std.Category.Instance.FiniteProductCategory where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Data.Product.Definition
open import Agora.Data.Lift.Definition
-- open import Agora.Data.Fin.Definition
-- open import Agora.Algebra.Monoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Category.Construction.Id
open import Agora.Category.Std.Limit.Specific.Product
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Constant
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Natural.Instance.Setoid
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Construction.Product


module _ {𝒞 𝒟 : 𝐂𝐚𝐭 𝑖} where
  instance
    isProduct:×-𝐂𝐚𝐭 : isProduct 𝒞 𝒟 (𝒞 × 𝒟)
    isProduct:×-𝐂𝐚𝐭 = record
                        { π₀        = π₀-𝐂𝐚𝐭
                        ; π₁        = π₁-𝐂𝐚𝐭
                        ; ⧼_⧽       = λ (f , g) -> ⧼ f , g ⧽-𝐂𝐚𝐭
                        ; isSetoidHom:⧼⧽ = {!!}
                        ; reduce-π₀ = λ {x} {f} {g} -> reduce-π₀-𝐂𝐚𝐭 {F = f} {G = g}
                        ; reduce-π₁ = λ {x} {f} {g} -> reduce-π₁-𝐂𝐚𝐭 {F = f} {G = g}
                        ; expand-π₀,π₁  = expand-⊓-𝐂𝐚𝐭
                        }


instance
  isTerminal:𝟙 : isTerminal {𝒞 = 𝐂𝐚𝐭 𝑖} ⊤-𝐂𝐚𝐭
  isTerminal:𝟙 = record
                 { intro-⊤   = intro-⊤-𝐂𝐚𝐭
                 ; expand-⊤  = expand-⊤-𝐂𝐚𝐭
                 }

instance
  hasProducts:𝐂𝐚𝐭 : hasProducts (𝐂𝐚𝐭 𝑖)
  hasProducts:𝐂𝐚𝐭 = record {_⊓_ = _×-𝐂𝐚𝐭_}

instance
  hasTerminal:𝐂𝐚𝐭 : hasTerminal (𝐂𝐚𝐭 𝑖)
  hasTerminal:𝐂𝐚𝐭 = record {⊤ = ⊤-𝐂𝐚𝐭}

instance
  hasFiniteProducts:𝐂𝐚𝐭 : hasFiniteProducts (𝐂𝐚𝐭 𝑖)
  hasFiniteProducts:𝐂𝐚𝐭 = hasFiniteProducts:default
  -- record { _⊓_ = _×-𝐂𝐚𝐭_ ; ⊤ = ⊤-𝐂𝐚𝐭 }

