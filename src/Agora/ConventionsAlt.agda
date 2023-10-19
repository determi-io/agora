
module Agora.Conventions where

open import Agda.Primitive public
open import Agda.Builtin.Equality public
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd) public
open import Data.Sum using () renaming (_⊎_ to _+_ ; inj₁ to left ; inj₂ to right) public

open import Data.Nat using (zero ; suc) renaming (ℕ to Nat ; _+_ to _+-ℕ_) public
open import Data.Bool public
open import Data.Unit using (tt) renaming (⊤ to Unit) public
open import Data.Fin using (Fin) public

open import Function.Base using (_∘_) public

variable
  𝑖 𝑗 𝑘 : Level

∑_ : ∀ {A : Set 𝑖} → (A → Set 𝑗) → Set (𝑖 ⊔ 𝑗)
∑_ = Σ _

∏_ : ∀ {A : Set 𝑖} → (A → Set 𝑗) → Set (𝑖 ⊔ 𝑗)
∏_ = λ F -> ∀ x -> F x

-- _∘_ : ∀{A : Set 𝑖} {B : Set 𝑗} {C : Set 𝑘} -> (B -> C) -> (A -> B) -> (A -> C)
-- f ∘ g = λ x -> f (g x)


isFinite : (A : Set 𝑖) -> Set 𝑖
isFinite A = ∑ λ (n : Nat) -> {!!}

-- isFinite-𝒫 : 


record Eval (A : Set 𝑖) (B : Set 𝑗) : Set (𝑖 ⊔ 𝑗) where
  field ⟦_⟧ : A -> B

open Eval {{...}} public

module _ {V : Set 𝑖} (E : V -> V -> Set 𝑗) where
  data Path : V -> V -> Set (𝑖 ⊔ 𝑗) where
    [] : ∀{v} -> Path v v
    _∷_ : ∀{a b c} -> E a b -> Path b c -> Path a c
