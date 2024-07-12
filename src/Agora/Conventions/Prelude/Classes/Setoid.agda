-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Conventions.Prelude.Classes.Setoid where

open import Agora.Conventions.Proprelude
open import Agora.Conventions.Prelude.Classes.Operators.Unary
-- open import Agora.Conventions.Prelude.Classes.Cast
-- open import Agora.Conventions.Prelude.Classes.Anything
open import Agora.Conventions.Prelude.Data.StrictId


-- AbstractOver : {P : 𝒰 𝑖} -> (P₀ : P) -> (Statement : P -> 𝒰 𝑗) -> Statement P₀
--         -> ∀{P₁ : P} -> {{P₁ ≡ P₀}} -> Statement P₁
-- AbstractOver {P} Statement P₀ proof {P₁} {{refl-≡}} = proof


-- [Definition]
record isEquivRel {A : 𝒰 𝑖} (_∼_ : A -> A -> 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
  -- constructor isEquivRel:byDef
  field refl-∼ : ∀{x : A} -> x ∼ x
        sym : ∀{x y : A} -> x ∼ y -> y ∼ x
        _∙_ : ∀{x y z : A} -> x ∼ y -> y ∼ z -> x ∼ z



  infixl 30 _∙_
open isEquivRel {{...}} public
-- //

module _ {X : 𝒰 𝑖} {_≡_ : X -> X -> 𝒰 𝑗} {{_ : isEquivRel _≡_}} where

  _≁_ : X -> X -> 𝒰 (𝑗)
  a ≁ b = ¬ a ≡ b

  instance
    Notation-Inverse:Equiv : {x y : X} -> Notation-Inverse (x ≡ y) (y ≡ x)
    Notation-Inverse:Equiv Notation-Inverse.⁻¹ = sym


-- [Definition]
-- | We call a type |A| a /setoid/ if it is equipped with an
--   equivalence relation.
--   That is, the type [..] is constructed by giving the following data.
record isSetoid {𝑗 𝑖 : 𝔏} (A : 𝒰 𝑖) : 𝒰 (𝑖 ⊔ 𝑗 ⁺) where
  -- instance constructor isSetoid:byDef

  field _∼_ : A -> A -> 𝒰 𝑗
  -- field {{isEquivRel:∼}} : isEquivRel _∼_
  field {{isEquivRel:∼}} : isEquivRel _∼_

        -- refl-∼  : ∀ {a : A} -> a ∼ a
        -- sym   : ∀ {a b : A} -> a ∼ b -> b ∼ a
        -- _∙_   : ∀ {a b c : A} -> a ∼ b -> b ∼ c -> a ∼ c

-- //
open isSetoid {{...}} public

-- {-# OVERLAPPABLE isSetoid:byDef #-}

-- open isSetoid {{...}} public hiding (isEquivRel:∼)
-- open isSetoid public using (isEquivRel:∼)

-- module _ {A : 𝒰 𝑖} where
--   instance
--     isSetoid:isEquivRel : {{_ : isSetoid {𝑗} A}} -> isEquivRel _∼_
--     isSetoid:isEquivRel {{X}} = isEquivRel:∼ X

--   -- field {{isEquivRel:∼}} : isEquivRel _∼_

-- {-# OVERLAPS isSetoid:isEquivRel #-}



-- [Hide]
-- module _ {X : 𝒰 𝑗} {{_ : isSetoid {𝑖} X}} where
--   open import Agora.Conventions.Prelude.Data.StrictId
--   instance
--     Notation-Inverse:Equiv : {x y : X} -> Notation-Inverse (x ∼ y) (y ∼ x)
--     Notation-Inverse:Equiv Notation-Inverse.⁻¹ = sym
-- //


-- [Example]
-- | Let [..] be a type.
module _ {A : 𝒰 𝑖} where
  -- |> Then the identity type on |A| is symmetric.
  -- The proof can be done by pattern matching on the
  -- given proof of |a ≡ b|, thus reducing the goal
  -- to |a ≡ a|, which we can conclude by |refl-≡|.
  sym-≡ : {a b : A} -> a ≡ b -> b ≡ a
  sym-≡ refl-≡ = refl-≡

  -- |> Similarly we can use pattern matching to prove transitivity.
  _∙-≡_ : {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
  _∙-≡_ refl-≡ q = q

  isEquivRel:≡ : isEquivRel {A = A} _≡_
  isEquivRel:≡ = record { refl-∼ = refl-≡ ; sym = sym-≡ ; _∙_ = _∙-≡_ }

  private instance _ = isEquivRel:≡

  -- |> This means that |A| together with the identity type
  -- is a setoid.
  isSetoid:byId : isSetoid A
  isSetoid:byId = record { _∼_ = _≡_ }
-- //

-- [Example]
-- | Let [..] be a type.
module _ {A : 𝒰 𝑖} where
  -- |> Then similarly the path relation |≡ : A -> A -> 𝒰| makes |A| into a setoid.
  -- The proofs that this is an equivalence relation can be taken from the builtin cubical library.
  -- isSetoid:byPath : isSetoid A
  -- isSetoid:byPath = isSetoid:byDef _≡_ refl-Path sym-Path trans-Path
-- //



-- [Hide]

-- refl-≡ = refl-Path
-- _∙-≡_ = trans-Path
-- _⁻¹-≡_ = sym-Path

module _ {A : 𝒰 𝑖} {{_ : isSetoid {𝑗} A}} where
  -- ≡→∼ : ∀{a b : A} -> a ≡ b -> a ∼ b
  -- ≡→∼ {a} p = transport (λ i -> a ∼ p i) refl

-- //

{-

-}
