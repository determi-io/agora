
module Agora.Data.Universe.Property.EpiMono where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Morphism.EpiMono
open import Agora.Data.Universe.Definition
open import Agora.Data.Universe.Instance.Category
open import Agora.Set.Function.Injective

module _ {A B : 𝒰 𝑖} where
  construct-isMono-𝐔𝐧𝐢𝐯 : ∀{f : A -> B} -> isInjective-𝒰 f -> isMono f
  isMono.cancel-mono (construct-isMono-𝐔𝐧𝐢𝐯 p) αf∼βf = λ i a → cancel-injective-𝒰 (λ j -> αf∼βf j a) i
    where instance _ = p

  destruct-isMono-𝐔𝐧𝐢𝐯 : ∀{f : A -> B} -> isMono f -> isInjective-𝒰 f
  isInjective-𝒰.cancel-injective-𝒰 (destruct-isMono-𝐔𝐧𝐢𝐯 {f} p) {a} {b} fa∼fb = λ i -> P₁ i tt
    where
      instance _ = p

      α : ⊤-𝒰 {𝑖} -> A
      α = const a

      β : ⊤-𝒰 {𝑖} -> A
      β = const b

      P₀ : α ◆ f ≡ β ◆ f
      P₀ = λ i _ → fa∼fb i

      P₁ : α ≡ β
      P₁ = cancel-mono P₀





