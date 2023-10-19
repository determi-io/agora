
--
-- NOTE: This file is originally from the cubical std library.
--       (https://github.com/agda/cubical)
--       It was copied here to replace references to cubical paths,
--       since cubical agda files cannot currently be compiled to binaries.
--       All copyright belongs to the original authors.
--
-- See:
-- module Cubical.Data.FinData.Base where
--

module Agora.Conventions.Prelude.Data.FinData.Base where

open import Agora.Conventions.Proprelude.CubicalConventions
open import Agora.Conventions.Prelude.Data.Nat.Base
open import Agora.Conventions.Prelude.Data.Nat.Properties
open import Agora.Conventions.Proprelude
open import Agora.Conventions.Prelude.Data.StrictId
open import Agora.Conventions.Prelude.Data.Bool
open import Agora.Conventions.Prelude.Classes.EquivalenceRelation

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Function
-- open import Cubical.Data.Nat
-- open import Cubical.Data.Bool.Base
-- open import Cubical.Relation.Nullary

private
  variable
    A B : Type ℓ

data Fin-R : ℕ → Type₀ where
  zero : {n : ℕ} → Fin-R (suc n)
  suc  : {n : ℕ} (i : Fin-R n) → Fin-R (suc n)

toℕ : ∀ {n} → Fin-R n → ℕ
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)

fromℕ : (n : ℕ) → Fin-R (suc n)
fromℕ zero    = zero
fromℕ (suc n) = suc (fromℕ n)

¬Fin-R0 : ¬ Fin-R 0
¬Fin-R0 ()

_==_ : ∀ {n} → Fin-R n → Fin-R n → Bool
zero == zero   = true
zero == suc _  = false
suc _ == zero  = false
suc m == suc n = m == n

foldrFin-R : ∀ {n} → (A → B → B) → B → (Fin-R n → A) → B
foldrFin-R {n = zero}  _ b _ = b
foldrFin-R {n = suc n} f b l = f (l zero) (foldrFin-R f b (l ∘ suc))
