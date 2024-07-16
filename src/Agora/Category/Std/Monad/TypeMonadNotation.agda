-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Monad.TypeMonadNotation where

open import Agora.Conventions

open import Agora.Setoid
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Category.Instance.Category

open import Agora.Category.Std.Monad.Definition

open import Agora.Data.Universe.Definition
open import Agora.Data.Universe.Instance.Category


module _ {T : _ -> _} {{_ : Monad (𝐓𝐲𝐩𝐞 𝑖) on T}} where
  _>>=_ : ∀{A B : 𝒰 𝑖} -> (T A) -> (A -> T B) -> T B
  a >>= f =
    let x = map f a
    in join _ x

  _>>_ : ∀{A B : 𝒰 𝑖} -> (T A) -> T B -> T B
  a >> b = a >>= const b

  return : {A : 𝒰 𝑖} -> A -> T A
  return = pure _


record isTraversable (T : Functor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖)) : 𝒰 (𝑖 ⁺) where
  constructor traversable
  field traverse : ∀{M : _ -> _} {{_ : Monad (𝐓𝐲𝐩𝐞 𝑖) on M}}
                 -> ∀{A}
                 -> ⟨ T ⟩ (M A) -> M (⟨ T ⟩ A)

open isTraversable {{...}} public

module _ (𝑖 : 𝔏) where
  Traversable = _ :& isTraversable {𝑖 = 𝑖}

-- module _ {T : 𝒰 𝑖 -> 𝒰 𝑖} {{_ : Traversable 𝑖 on T}}
--          {M : 𝒰 𝑖 -> 𝒰 𝑖} {{_ : Monad (𝐔𝐧𝐢𝐯 𝑖) on M}} where

module _ {T : 𝒰 𝑖 -> 𝒰 𝑖} {{_ : isFunctor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) T}}
                          {{_ : isTraversable ′ T ′}}
         {M : 𝒰 𝑖 -> 𝒰 𝑖} {{_ : isFunctor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) M}}
                          {{_ : isMonad ′ M ′}} where

  mapM : ∀{A B : 𝒰 𝑖} -> (f : A -> M B) -> T A -> M (T B)
  mapM f xs = traverse (map f xs)



