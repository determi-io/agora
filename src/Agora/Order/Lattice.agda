-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

-- {-# OPTIONS --overlapping-instances #-}

module Agora.Order.Lattice where

open import Agora.Conventions
open import Agora.Setoid.Definition
-- open import Agora.Category.Definition
-- open import Agora.Category.Instance.Set.Definition
open import Agora.Order.Preorder


module _ {A : 𝒰 _} {{_ : Preorder 𝑗 on A}} where
  _≚_ : A -> A -> 𝒰 _
  a ≚ b = (a ≤ b) ×-𝒰 (b ≤ a)

module _ {𝑖 : 𝔏 ^ 3} where
  record hasFiniteJoins (A : Preorder 𝑖) : 𝒰 (merge 𝑖) where
    field ⊥ : ⟨ A ⟩
          initial-⊥ : ∀{a : ⟨ A ⟩} -> ⊥ ≤ a
    field _∨_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
          ι₀-∨ : {a b : ⟨ A ⟩} -> a ≤ a ∨ b
          ι₁-∨ : {a b : ⟨ A ⟩} -> b ≤ a ∨ b
          [_,_]-∨ : {a b c : ⟨ A ⟩} -> a ≤ c -> b ≤ c -> a ∨ b ≤ c

    infixl 60 _∨_
  open hasFiniteJoins {{...}} public

  {-# DISPLAY hasFiniteJoins._∨_ M a b = a ∨ b #-}

  record hasFiniteMeets (A : Preorder 𝑖) : 𝒰 (merge 𝑖) where
    field ⊤ : ⟨ A ⟩
          terminal-⊤ : ∀{a : ⟨ A ⟩} -> a ≤ ⊤
    field _∧_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
          π₀-∧ : {a b : ⟨ A ⟩} -> a ∧ b ≤ a
          π₁-∧ : {a b : ⟨ A ⟩} -> a ∧ b ≤ b
          ⟨_,_⟩-∧ : {a b c : ⟨ A ⟩} -> c ≤ a -> c ≤ b -> c ≤ a ∧ b

    infixl 80 _∧_
  open hasFiniteMeets {{...}} public

  {-# DISPLAY hasFiniteMeets._∧_ M a b = a ∧ b #-}

  record hasAllJoins (𝑗 : 𝔏) (A : Preorder 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺)) where
    field ⋁ : ∀{X : 𝒰 𝑗} -> (X -> ⟨ A ⟩) -> ⟨ A ⟩
          ι-⋁ : ∀{X F} -> ∀ (x : X) -> F x ≤ ⋁ F
          [_]-⋁ : ∀{X F b} -> (∀(x : X) -> F x ≤ b) -> ⋁ F ≤ b
  open hasAllJoins {{...}} public

  record hasAllMeets (𝑗 : 𝔏) (A : Preorder 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺)) where
    field ⋀ : ∀{X : 𝒰 𝑗} -> (X -> ⟨ A ⟩) -> ⟨ A ⟩
          π-⋀ : ∀{X F} -> ∀ (x : X) -> ⋀ F ≤ F x
          ⟨_⟩-⋀ : ∀{X F b} -> (∀(x : X) -> b ≤ F x) -> b ≤ ⋀ F
  open hasAllMeets {{...}} public

CompleteJoinSemilattice : ∀ (𝑖 : 𝔏 ^ 4) -> 𝒰 (𝑖 ⁺)
CompleteJoinSemilattice 𝑖 = Preorder (𝑖 ⌄ 0 , 𝑖 ⌄ 1 , 𝑖 ⌄ 2) :& hasAllJoins (𝑖 ⌄ 3)

MeetSemilattice : ∀ 𝑖 -> 𝒰 (𝑖 ⁺)
MeetSemilattice 𝑖 = Preorder 𝑖 :& hasFiniteMeets

JoinSemilattice : ∀ 𝑖 -> 𝒰 (𝑖 ⁺)
JoinSemilattice 𝑖 = Preorder 𝑖 :& hasFiniteJoins

record isLattice (A : Preorder 𝑖 :& (hasFiniteMeets :, hasFiniteJoins)) : 𝒰 𝑖 where

instance
  isLattice:Default : ∀{A : 𝒰 _} -> {{_ : Preorder 𝑖 on A}}
                      {{_ : hasFiniteMeets ′ A ′}}
                      {{_ : hasFiniteJoins ′ A ′}}
                      -> isLattice ′ A ′
  isLattice:Default = record {}

Lattice : (𝑖 : 𝔏 ^ 3) -> 𝒰 _
Lattice 𝑖 = Preorder 𝑖 :& (hasFiniteMeets :, hasFiniteJoins) :& isLattice

----------------------------------------------------------
-- Derived instances

module _ {A : 𝒰 _} {{_ : A is JoinSemilattice 𝑖}} {B : 𝒰 _} {{_ : B is JoinSemilattice 𝑗}} where
  open import Agora.Data.Product.Definition

  instance
    hasFiniteJoins:× : hasFiniteJoins (A × B)
    hasFiniteJoins:× = record
      { ⊥ = ⊥ , ⊥
      ; initial-⊥ = initial-⊥ , initial-⊥
      ; _∨_ = λ (a0 , b0) (a1 , b1) -> (a0 ∨ a1) , (b0 ∨ b1)
      ; ι₀-∨ = ι₀-∨ , ι₀-∨
      ; ι₁-∨ = ι₁-∨ , ι₁-∨
      ; [_,_]-∨ = λ (pa , pb) (qa , qb) -> [ pa , qa ]-∨ , [ pb , qb ]-∨
      }

module _ {A : 𝒰 _} {{_ : A is MeetSemilattice 𝑖}} {B : 𝒰 _} {{_ : B is MeetSemilattice 𝑗}} where
  open import Agora.Data.Product.Definition

  instance
    hasFiniteMeets:× : hasFiniteMeets (A × B)
    hasFiniteMeets:× = record
      { ⊤ = ⊤ , ⊤
      ; terminal-⊤ = terminal-⊤ , terminal-⊤
      ; _∧_ = λ (a0 , b0) (a1 , b1) -> (a0 ∧ a1) , (b0 ∧ b1)
      ; π₀-∧ = π₀-∧ , π₀-∧
      ; π₁-∧ = π₁-∧ , π₁-∧
      ; ⟨_,_⟩-∧ = λ (pa , pb) (qa , qb) -> ⟨ pa , qa ⟩-∧ , ⟨ pb , qb ⟩-∧
      }

module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasFiniteJoins ′ A ′}} where
  instance
    hasFiniteJoins:Family : ∀{I : 𝒰 𝑗} -> hasFiniteJoins (′ (I -> A) ′)
    hasFiniteJoins.⊥         hasFiniteJoins:Family = λ _ -> ⊥
    hasFiniteJoins.initial-⊥ hasFiniteJoins:Family = λ _ -> initial-⊥
    hasFiniteJoins._∨_       hasFiniteJoins:Family = λ a b i -> a i ∨ b i
    hasFiniteJoins.ι₀-∨      hasFiniteJoins:Family = λ a -> ι₀-∨
    hasFiniteJoins.ι₁-∨      hasFiniteJoins:Family = λ a -> ι₁-∨
    hasFiniteJoins.[_,_]-∨   hasFiniteJoins:Family = λ f g a -> [ f a , g a ]-∨



module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasFiniteMeets ′ A ′}} where
  instance
    hasFiniteMeets:Family : ∀{I : 𝒰 𝑗} -> hasFiniteMeets (′ (I -> A) ′)
    hasFiniteMeets.⊤          hasFiniteMeets:Family = λ _ -> ⊤
    hasFiniteMeets.terminal-⊤ hasFiniteMeets:Family = λ a -> terminal-⊤
    hasFiniteMeets._∧_        hasFiniteMeets:Family = λ a b i -> a i ∧ b i
    hasFiniteMeets.π₀-∧       hasFiniteMeets:Family = λ a -> π₀-∧
    hasFiniteMeets.π₁-∧       hasFiniteMeets:Family = λ a -> π₁-∧
    hasFiniteMeets.⟨_,_⟩-∧    hasFiniteMeets:Family = λ f g a -> ⟨ f a , g a ⟩-∧


module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasFiniteMeets ′ A ′}} where

  map-∧ : ∀{a b c d : A} -> (a ≤ b) -> (c ≤ d) -> a ∧ c ≤ b ∧ d
  map-∧ f g = ⟨ π₀-∧ ⟡ f , π₁-∧ ⟡ g ⟩-∧

  module _ {{_ : isPartialorder ′ A ′}} where
    _≀∧≀_ : {a b c d : A} -> (a ∼ b) -> (c ∼ d) -> a ∧ c ∼ b ∧ d
    _≀∧≀_ p q = antisym (map-∧ (by-∼-≤ p) (by-∼-≤ q)) (map-∧ (by-∼-≤ (p ⁻¹)) (by-∼-≤ (q ⁻¹)))

    sym-∧ : ∀{a b : A} -> a ∧ b ∼ b ∧ a
    sym-∧ = antisym (⟨ π₁-∧ , π₀-∧ ⟩-∧) (⟨ π₁-∧ , π₀-∧ ⟩-∧)

    unit-r-∧ : ∀{a : A} -> a ∧ ⊤ ∼ a
    unit-r-∧ = antisym π₀-∧ ⟨ refl-≤ , terminal-⊤ ⟩-∧

    unit-l-∧ : ∀{a : A} -> ⊤ ∧ a ∼ a
    unit-l-∧ = sym-∧ ∙ unit-r-∧

    assoc-l-∧ : ∀{a b c : A} -> (a ∧ b) ∧ c ∼ a ∧ (b ∧ c)
    assoc-l-∧ = antisym
      ⟨ π₀-∧ ⟡ π₀-∧ , ⟨ π₀-∧ ⟡ π₁-∧ , π₁-∧ ⟩-∧ ⟩-∧
      ⟨ ⟨ π₀-∧ , π₁-∧ ⟡ π₀-∧ ⟩-∧ , π₁-∧ ⟡ π₁-∧ ⟩-∧

    assoc-r-∧ : ∀{a b c : A} -> a ∧ (b ∧ c) ∼ (a ∧ b) ∧ c
    assoc-r-∧ = assoc-l-∧ ⁻¹

    idem-∧ : ∀{a : A} -> a ∧ a ∼ a
    idem-∧ = antisym π₀-∧ ⟨ refl-≤ , refl-≤ ⟩-∧

  ⋀-fin : ∀{n} -> (F : Fin-R n -> A) -> A
  ⋀-fin {zero} F = ⊤
  ⋀-fin {suc n} F = F zero ∧ (⋀-fin (λ i -> F (suc i)))

  -- meets are preserved by equivalence
  transp-terminal-⊤ : ∀{x : A} -> x ∼ ⊤ -> ∀{a} -> a ≤ x
  transp-terminal-⊤ p = transp-≤ refl-∼ (sym p) terminal-⊤

  transp-π₀-∧ : ∀{x y z : A} -> x ∼ (y ∧ z) -> x ≤ y
  transp-π₀-∧ p = transp-≤ (sym p) refl-∼ π₀-∧

  transp-π₁-∧ : ∀{x y z : A} -> x ∼ (y ∧ z) -> x ≤ z
  transp-π₁-∧ p = transp-≤ (sym p) refl-∼ π₁-∧

  transp-⟨⟩-∧ : ∀{x y z w : A} -> x ∼ (y ∧ z) -> w ≤ y -> w ≤ z -> w ≤ x
  transp-⟨⟩-∧ p ϕ ψ = transp-≤ refl-∼ (sym p) ⟨ ϕ , ψ ⟩-∧

module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasFiniteJoins ′ A ′}} where

  -- joins are preserved by equivalence
  transp-initial-⊥ : ∀{x : A} -> x ∼ ⊥ -> ∀{a} -> x ≤ a
  transp-initial-⊥ p = transp-≤ (sym p) refl-∼ initial-⊥

  transp-ι₀-∨ : ∀{x y z : A} -> x ∼ (y ∨ z) -> y ≤ x
  transp-ι₀-∨ p = transp-≤ refl-∼ (sym p) ι₀-∨

  transp-ι₁-∨ : ∀{x y z : A} -> x ∼ (y ∨ z) -> z ≤ x
  transp-ι₁-∨ p = transp-≤ refl-∼ (sym p) ι₁-∨

  transp-[]-∨ : ∀{x y z w : A} -> x ∼ (y ∨ z) -> y ≤ w -> z ≤ w -> x ≤ w
  transp-[]-∨ p ϕ ψ = transp-≤ (sym p) refl-∼ [ ϕ , ψ ]-∨


module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasAllJoins 𝑙 ′ A ′}} where
  instance
    hasAllJoins:Family : ∀{I : 𝒰 𝑗} -> hasAllJoins 𝑙 (′ (I -> A) ′)
    hasAllJoins.⋁ hasAllJoins:Family F = λ i -> ⋁ (λ x -> F x i)
    hasAllJoins.ι-⋁ hasAllJoins:Family = λ x → λ a → ι-⋁ x
    hasAllJoins.[ hasAllJoins:Family ]-⋁ = λ F a → [ (λ x → F x a) ]-⋁


  module _ {{_ : isPartialorder ′ A ′}}
         {{_ : hasFiniteJoins ′ A ′}} where

    empty-⋁ : ∀{B : 𝒰 𝑙} -> (B -> 𝟘-𝒰) -> {F : B -> A} -> ⋁ F ∼ ⊥
    empty-⋁ P {F} = antisym [ (λ b -> 𝟘-rec (P b)) ]-⋁ (initial-⊥)

    duplicate-r-⋁ : ∀{B : 𝒰 𝑙} -> {F : B -> A} -> (b : B) -> {a : A}
                    -> F b ∼ a -> ⋁ F ∨ a ∼ ⋁ F
    duplicate-r-⋁ b {a} p = antisym [ refl-≤ , (by-∼-≤ (p ⁻¹)) ⟡ ι-⋁ b ]-∨ (ι₀-∨)

module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasAllMeets 𝑙 ′ A ′}} where
  instance
    hasAllMeets:Family : ∀{I : 𝒰 𝑗} -> hasAllMeets 𝑙 (′ (I -> A) ′)
    hasAllMeets.⋀ hasAllMeets:Family F = λ i -> ⋀ (λ x -> F x i)
    hasAllMeets.π-⋀ hasAllMeets:Family = λ x → λ a → π-⋀ x
    hasAllMeets.⟨ hasAllMeets:Family ⟩-⋀ = λ F a → ⟨ (λ x → F x a) ⟩-⋀

module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : isPartialorder ′ A ′}}
         {{_ : hasFiniteJoins ′ A ′}}
         {{_ : hasFiniteMeets ′ A ′}} where

  absorb-l-∧ : ∀{a : A} -> ⊥ ∧ a ∼ ⊥
  absorb-l-∧ = antisym π₀-∧ initial-⊥

  absorb-r-∨ : ∀{a : A} -> a ∨ ⊤ ∼ ⊤
  absorb-r-∨ = antisym terminal-⊤ ι₁-∨




----------------------------------------------------------
-- Categorical Structure


-- unquoteDecl CompleteJoinSemilattice makeCompleteJoinSemilattice = #struct "CompleteJoinSemilattice" (quote hasAllJoins) "A" CompleteJoinSemilattice makeCompleteJoinSemilattice

-- instance
--   POStruc : ∀{a : CompleteJoinSemilattice 𝑖}


-- record isCompleteJoinPreserving {A : CompleteJoinSemilattice 𝑖} {B : CompleteJoinSemilattice 𝑗} (f : (⟨ A ⟩ -> El B) :& isMonotone {A = make& (⟨ A ⟩)}) : 𝒰 (𝑖 ､ 𝑗) where
--   testa : isPreorder (⟨ A ⟩)
--   testa = it


-- testing1 : (A : CompleteJoinSemilattice 𝑖) -> (X : 𝒰 𝑖) -> (F : X -> ⟨ A ⟩) -> 𝒰 𝑖
-- testing1 A X F = ∑ (λ (a : ⟨ A ⟩) -> ∀(x : X) -> a ≤ F x)


{-
record preservesAllJoins {A B} {{_ : CompleteJoinSemilattice 𝑖 on A}} {{_ : CompleteJoinSemilattice 𝑖 on B}} (f : (A -> B) :& isMonotone) : 𝒰 (𝑖 ⁺) where
  field preserves-⋁ : ∀{X} {F : X -> A} -> ⟨ f ⟩ (⋁ F) ≚ ⋁ (λ x -> ⟨ f ⟩ (F x))


record preservesFiniteMeets {A B} {{_ : MeetSemilattice 𝑖 on A}} {{_ : MeetSemilattice 𝑗 on B}} (f : (A -> B) :& isMonotone) : 𝒰 (𝑖 ､ 𝑗) where
  field preserves-∧ : ∀{a b : A} -> ⟨ f ⟩ (a ∧ b) ≚ ⟨ f ⟩ a ∧ ⟨ f ⟩ b
        preserves-⊤ : ⟨ f ⟩ ⊤ ≚ ⊤

-}



