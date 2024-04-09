
module Agora.Setoid.Morphism.Injective where

open import Agora.Conventions
open import Agora.Setoid.Definition


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isSetoid {𝑖₁} A}} {{_ : isSetoid {𝑗₁} B}} where
  record isInjective (f : A -> B) {{_ : isSetoidHom ′ A ′ ′ B ′ f}} : 𝒰 (𝑖 ､ 𝑖₁ ､ 𝑗 ､ 𝑗₁) where
    field cancel-injective : ∀ {a b} -> f a ∼ f b -> a ∼ b

  open isInjective {{...}} public




