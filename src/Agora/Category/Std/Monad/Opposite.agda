
module Agora.Category.Std.Monad.Opposite where

open import Agora.Conventions

open import Agora.Setoid
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Category.Opposite
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Monad.Definition



module _ {𝒞 : Category 𝑖} where
  OpFunctor : (Functor 𝒞 𝒞) -> Functor (𝒞 ᵒᵖ) (𝒞 ᵒᵖ)
  OpFunctor F = ⟨ F ⟩ since P
    where
      P : isFunctor (𝒞 ᵒᵖ) (𝒞 ᵒᵖ) ⟨ F ⟩
      isFunctor.map P = map
      isFunctor.isSetoidHom:map P = it
      isFunctor.functoriality-id P = functoriality-id
      isFunctor.functoriality-◆ P = functoriality-◆

  -- note, this does not work. We do have that "F ᵒᵖ" is a comonad!
  OpMonad : ∀{F : 𝒞 ⟶ 𝒞} -> {{_ : isMonad F}} -> isMonad (OpFunctor F)
  OpMonad = {!!}




