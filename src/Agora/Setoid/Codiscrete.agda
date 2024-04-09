
module Agora.Setoid.Codiscrete where

open import Agora.Conventions
-- open import Agora.Data.Prop.Definition
-- open import Agora.Data.Product.Definition
open import Agora.Setoid.Definition
-- open import Agora.Category.Std.Category.Definition


isSetoid:byCodiscrete : ∀{A : 𝒰 𝑖} -> isSetoid {𝑗} A
isSetoid._∼_ isSetoid:byCodiscrete  = λ _ _ -> ⊤-𝒰
isSetoid.refl isSetoid:byCodiscrete = tt
isSetoid.sym isSetoid:byCodiscrete  = λ x₁ → tt
isSetoid._∙_ isSetoid:byCodiscrete  = λ x₁ x₂ → tt



