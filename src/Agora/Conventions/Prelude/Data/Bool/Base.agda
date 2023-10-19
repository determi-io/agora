
--
-- NOTE: This file is originally from the cubical std library.
--       (https://github.com/agda/cubical)
--       It was copied here to replace references to cubical paths,
--       since cubical agda files cannot currently be compiled to binaries.
--       All copyright belongs to the original authors.
--
-- See:
-- module Cubical.Data.Bool.Base where
--

module Agora.Conventions.Prelude.Data.Bool.Base where

open import Agora.Conventions.Proprelude.CubicalConventions
open import Agora.Conventions.Prelude.Classes.Discrete
open import Agora.Conventions.Prelude.Classes.EquivalenceRelation
open import Agora.Conventions.Prelude.Classes.Setoid
open import Agora.Conventions.Prelude.Data.StrictId
open import Agora.Conventions.Prelude.Data.Sum
open import Agora.Conventions.Proprelude


-- open import Cubical.Core.Everything

-- open import Cubical.Foundations.Prelude

-- open import Cubical.Data.Empty
-- open import Cubical.Data.Sum.Base

-- open import Cubical.Relation.Nullary
-- open import Cubical.Relation.Nullary.DecidableEq

-- Obtain the booleans
open import Agda.Builtin.Bool public

private
  variable
    -- ℓ : Level
    A : Type ℓ

infixr 6 _and_
infixr 5 _or_
infix  0 if_then_else_

instance
  isSetoid:Bool : isSetoid Bool
  isSetoid:Bool = isSetoid:byId


not : Bool → Bool
not true = false
not false = true

_or_ : Bool → Bool → Bool
false or false = false
false or true  = true
true  or false = true
true  or true  = true

_and_ : Bool → Bool → Bool
false and false = false
false and true  = false
true  and false = false
true  and true  = true

-- xor / mod-2 addition
_⊕_ : Bool → Bool → Bool
false ⊕ x = x
true  ⊕ x = not x

if_then_else_ : Bool → A → A → A
if true  then x else y = x
if false then x else y = y

_≟_ : Discrete Bool
false ≟ false = right refl
false ≟ true  = left λ ()
-- λ p →  (λ b → if b then 𝟘-𝒰 else Bool) p true
true  ≟ false = left λ ()
-- λ p → subst (λ b → if b then Bool else 𝟘-𝒰) p true
true  ≟ true  = right refl

Dec→Bool : Decision A → Bool
Dec→Bool (yes p) = true
Dec→Bool (no ¬p) = false

dichotomyBool : (x : Bool) → (x ≣ true) +-𝒰 (x ≣ false)
dichotomyBool true  = left refl
dichotomyBool false = right refl

-- TODO: this should be uncommented and implemented using instance arguments
-- _==_ : {dA : Discrete A} → A → A → Bool
-- _==_ {dA = dA} x y = Dec→Bool (dA x y)
