
{-# OPTIONS --allow-unsolved-metas #-}

module Agora.TypeTheory.ParamSTT.Definition where

open import Agora.Conventions hiding (m ; n ; _∙_ ; _∣_)
open import Agora.Data.Fin.Definition
open import Agora.TypeTheory.STT.Definition




record hasParamSTT {𝑗 : 𝔏 ^ 5} {𝑖} (Theory : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field Param : Theory -> 𝒰 (𝑗 ⌄ 0)
  field SubParam : (This : Theory) -> Param This -> 𝒰 (𝑗 ⌄ 1)
  field _at_ : (𝒯 : Theory) -> Param 𝒯 -> STT (𝑗 ⌄ 2 ⋯ 4)
  open STT

  CtxOf : (𝒯 : Theory) -> Param 𝒯 -> 𝒰 _
  CtxOf 𝒯 a = Ctx (𝒯 at a)

  syntax CtxOf 𝒯 a = Ctx a of 𝒯

  TypeOf : (𝒯 : Theory) -> Param 𝒯 -> 𝒰 _
  TypeOf 𝒯 a = Type (𝒯 at a)

  syntax TypeOf 𝒯 a = Type a of 𝒯

open hasParamSTT {{...}} public

ParamSTT : ∀ (𝑗 : 𝔏 ^ 6) -> _
ParamSTT 𝑗 = 𝒰 (𝑗 ⌄ 0) :& hasParamSTT {𝑗 ⌄ 1 ⋯ 5}


record isParamSTTHom (𝔄 : ParamSTT 𝑖) (𝔅 : ParamSTT 𝑗) (F : ⟨ 𝔄 ⟩ -> ⟨ 𝔅 ⟩) : 𝒰 (𝑖 ､ 𝑗) where
  field param : ∀(A : ⟨ 𝔄 ⟩) -> Param (F A) -> Param A
  field runAt : ∀(A : ⟨ 𝔄 ⟩) -> {a : Param (F A)} -> Hom-STT (F A at a) (A at param A a)

open isParamSTTHom {{...}} public

module _ (𝔄 : ParamSTT 𝑖) (𝔅 : ParamSTT 𝑗) where
  ParamSTTHom : _
  ParamSTTHom = _ :& isParamSTTHom 𝔄 𝔅


module _ {𝔄 : ParamSTT 𝑖} {𝔅 : ParamSTT 𝑗} where
  record _∼-ParamSTTHom_ (f g : ParamSTTHom 𝔄 𝔅) : 𝒰 (𝑖 ､ 𝑗) where

  instance
    isEquivRel:∼-ParamSTTHom : isEquivRel (_∼-ParamSTTHom_)
    isEquivRel:∼-ParamSTTHom = record
      { refl-∼ = {!!}
      ; sym = {!!}
      ; _∙_ = {!!}
      }

  instance
    isSetoid:ParamSTTHom : isSetoid (ParamSTTHom 𝔄 𝔅)
    isSetoid:ParamSTTHom = record { _∼_ = _∼-ParamSTTHom_ }



module _ {𝔄 : ParamSTT 𝑖} {𝔅 : ParamSTT 𝑗} where
  run_to_ : (F : ParamSTTHom 𝔄 𝔅) -> (A : ⟨ 𝔄 ⟩) -> {a : Param (⟨ F ⟩ A)} -> _
  run_to_ F A {a} = runAt A {a = a}

  par : (F : ParamSTTHom 𝔄 𝔅) -> {A : ⟨ 𝔄 ⟩} -> Param (⟨ F ⟩ A) -> Param A
  par F {A} = param A



