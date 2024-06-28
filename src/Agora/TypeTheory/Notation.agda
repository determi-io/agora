
module Agora.TypeTheory.Notation where

open import Agora.Conventions hiding (m ; n ; _∙_ ; _∣_)


record isTypeTheory {𝑘} (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑘 ⁺) where
  field {CtxType} : A -> 𝒰 𝑘
  field ⊢Ctx : {{a : A}} -> CtxType a
  [_]-Ctx : (a : A) -> CtxType a
  [_]-Ctx a = ⊢Ctx {{a}}
  field {TypeType} : A -> 𝒰 𝑘
  field ⊢Type : {{a : A}} -> TypeType a
  field {TurnstyleType} : A -> 𝒰 𝑘
  field _⊢_ : {{a : A}} -> TurnstyleType a
  _▻_⊢_ : (a : A) -> TurnstyleType a
  _▻_⊢_ a = _⊢_ {{a}}

open isTypeTheory {{...}} public


record SimpleTypeTheory {𝑗 : 𝔏 ^ 3}  : 𝒰 ( 𝑗 ⁺) where
  field Ctx : 𝒰 (𝑗 ⌄ 0)
  field Type : 𝒰 (𝑗 ⌄ 1)
  field Term : Ctx -> Type -> 𝒰 (𝑗 ⌄ 2)


record hasSTT {𝑗 : 𝔏 ^ 4} {𝑖} (Theory : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field Param : Theory -> 𝒰 (𝑗 ⌄ 0)
  field _at_ : (𝒯 : Theory) -> Param 𝒯 -> SimpleTypeTheory {𝑗 ⌄ 1 ⋯ 3}
  -- field Ctx : ∀{𝒯 : Theory} -> Param 𝒯 -> 𝒰 (𝑗 ⌄ 1)
  -- field Type : ∀{𝒯 : Theory} -> Param 𝒯 -> 𝒰 (𝑗 ⌄ 2)
  -- field Term : ∀{𝒯 : Theory} -> {a : Param 𝒯} -> Ctx a -> Type a -> 𝒰 (𝑗 ⌄ 3)
  open SimpleTypeTheory

  CtxOf : (𝒯 : Theory) -> Param 𝒯 -> 𝒰 _
  CtxOf 𝒯 a = Ctx (𝒯 at a)

  syntax CtxOf 𝒯 a = Ctx a of 𝒯

open hasSTT {{...}} public

STT : ∀ (𝑗 : 𝔏 ^ 5) -> _
STT 𝑗 = 𝒰 (𝑗 ⌄ 0) :& hasSTT {𝑗 ⌄ 1 ⋯ 4}


record isReduction (A : STT 𝑖) (B : STT 𝑗) (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
  ⟦_⟧ : ∀{a : Param ⟨ A ⟩} -> Ctx (f a) of B -> Ctx a of A



-- record isSimpleTypeTheory {𝑗 : 𝔏 ^ 4} {𝑖} (Theory : 𝒰 𝑖) : 𝒰 (𝑖 , 𝑗 ⁺) where
--   field Param : 𝒰 (𝑗 ⌄ 0)
--   field Ctx : Param -> 𝒰 (𝑗 ⌄ 1)
--   field Type : Param -> 𝒰 (𝑗 ⌄ 2)
--   field Term : {a : Param} -> Ctx a -> Type a -> 𝒰 (𝑗 ⌄ 3)

-- open isSimpleTypeTheory {{...}} public

-- record isSimpleTypeTheory {𝑗 : 𝔏 ^ 3} {𝑖} (Param : 𝒰 𝑖) : 𝒰 (𝑖 , 𝑗 ⁺) where
--   field Ctx : Param -> 𝒰 (𝑗 ⌄ 0)
--   field Type : Param -> 𝒰 (𝑗 ⌄ 1)
--   field Term : {a : Param} -> Ctx a -> Type a -> 𝒰 (𝑗 ⌄ 2)

-- open isSimpleTypeTheory {{...}} public

{-
record isSimpleTypeTheory {𝑗 : 𝔏 ^ 4} {𝑖} (Theory : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field Param : Theory -> 𝒰 (𝑗 ⌄ 0)
  field Ctx : ∀{𝒯 : Theory} -> Param 𝒯 -> 𝒰 (𝑗 ⌄ 1)
  field Type : ∀{𝒯 : Theory} -> Param 𝒯 -> 𝒰 (𝑗 ⌄ 2)
  field Term : ∀{𝒯 : Theory} -> {a : Param 𝒯} -> Ctx a -> Type a -> 𝒰 (𝑗 ⌄ 3)


open isSimpleTypeTheory {{...}} public

module _ {Theory : 𝒰 𝑖} {{_ : isSimpleTypeTheory {𝑗} Theory}} where
  Ctx' : (𝒯 : Theory) -> Param 𝒯 -> 𝒰 _
  Ctx' 𝒯 a = Ctx {𝒯 = 𝒯} a

  syntax Ctx' 𝒯 a = Ctx a of 𝒯


-}

-- SMTT : SimpleTypeTheory

-- let 𝒯 : SMTT, Γ : Ctx a of 𝒯  , t : 𝒯 , Γ ⊢ A of 𝒯




