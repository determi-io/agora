-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.TypeTheory.Notation where

-- open import Agora.Conventions hiding (m ; n ; _∙_ ; _∣_)
-- open import Agora.Data.Fin.Definition


-- -- record isTypeTheory {𝑘} (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑘 ⁺) where
-- --   field {CtxType} : A -> 𝒰 𝑘
-- --   field ⊢Ctx : {{a : A}} -> CtxType a
-- --   [_]-Ctx : (a : A) -> CtxType a
-- --   [_]-Ctx a = ⊢Ctx {{a}}
-- --   field {TypeType} : A -> 𝒰 𝑘
-- --   field ⊢Type : {{a : A}} -> TypeType a
-- --   field {TurnstyleType} : A -> 𝒰 𝑘
-- --   field _⊢_ : {{a : A}} -> TurnstyleType a
-- --   _▻_⊢_ : (a : A) -> TurnstyleType a
-- --   _▻_⊢_ a = _⊢_ {{a}}

-- -- open isTypeTheory {{...}} public





-- record STT (𝑗 : 𝔏 ^ 3) : 𝒰 ( 𝑗 ⁺) where
--   field Ctx : 𝒰 (𝑗 ⌄ 0)
--   field Type : 𝒰 (𝑗 ⌄ 1)
--   field Term : Ctx -> Type -> 𝒰 (𝑗 ⌄ 2)

-- open STT public


-- record Hom-STT (𝔄 : STT 𝑖) (𝔅 : STT 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
--   field ⟪_∣_Ctx⟫ : Ctx 𝔄 -> Ctx 𝔅
--   field ⟪_∣_Type⟫ : Type 𝔄 -> Type 𝔅
--   field ⟪_∣_Term⟫ : ∀{Γ A} -> Term 𝔄 Γ A -> Term 𝔅 (⟪_∣_Ctx⟫ Γ) (⟪_∣_Type⟫ A)


-- open Hom-STT public



-- record hasParamSTT {𝑗 : 𝔏 ^ 4} {𝑖} (Theory : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
--   field Param : Theory -> 𝒰 (𝑗 ⌄ 0)
--   field _at_ : (𝒯 : Theory) -> Param 𝒯 -> STT (𝑗 ⌄ 1 ⋯ 3)
--   open STT

--   CtxOf : (𝒯 : Theory) -> Param 𝒯 -> 𝒰 _
--   CtxOf 𝒯 a = Ctx (𝒯 at a)

--   syntax CtxOf 𝒯 a = Ctx a of 𝒯

--   TypeOf : (𝒯 : Theory) -> Param 𝒯 -> 𝒰 _
--   TypeOf 𝒯 a = Type (𝒯 at a)

--   syntax TypeOf 𝒯 a = Type a of 𝒯

-- open hasParamSTT {{...}} public

-- ParamSTT : ∀ (𝑗 : 𝔏 ^ 5) -> _
-- ParamSTT 𝑗 = 𝒰 (𝑗 ⌄ 0) :& hasParamSTT {𝑗 ⌄ 1 ⋯ 4}


-- record isReduction (𝔄 : ParamSTT 𝑖) (𝔅 : ParamSTT 𝑗) (F : ⟨ 𝔄 ⟩ -> ⟨ 𝔅 ⟩) : 𝒰 (𝑖 ､ 𝑗) where
--   field param : ∀(A : ⟨ 𝔄 ⟩) -> Param (F A) -> Param A
--   field runAt : ∀(A : ⟨ 𝔄 ⟩) -> {a : Param (F A)} -> Hom-STT (F A at a) (A at param A a)
--   -- field ⟦_⟧-Ctx : ∀{A : ⟨ 𝔄 ⟩} -> {a : Param (F A)} -> Ctx a of (F A) -> Ctx ⟦ a ⟧-Param of A
--   -- field ⟦_⟧-Type : ∀{A : ⟨ 𝔄 ⟩} -> {a : Param (F A)} -> Ctx a of (F A) -> Ctx ⟦ a ⟧-Param of A

--   -- syntax runAt A F = run F at A

-- open isReduction {{...}} public

-- module _ (𝔄 : ParamSTT 𝑖) (𝔅 : ParamSTT 𝑗) where
--   Reduction : _
--   Reduction = _ :& isReduction 𝔄 𝔅


-- module _ {𝔄 : ParamSTT 𝑖} {𝔅 : ParamSTT 𝑗} where
--   run_to_ : (F : Reduction 𝔄 𝔅) -> (A : ⟨ 𝔄 ⟩) -> {a : Param (⟨ F ⟩ A)} -> _
--   run_to_ F A {a} = runAt A {a = a}

--   par : (F : Reduction 𝔄 𝔅) -> {A : ⟨ 𝔄 ⟩} -> Param (⟨ F ⟩ A) -> Param A
--   par F {A} = param A



-- -- record isSTT {𝑗 : 𝔏 ^ 4} {𝑖} (Theory : 𝒰 𝑖) : 𝒰 (𝑖 , 𝑗 ⁺) where
-- --   field Param : 𝒰 (𝑗 ⌄ 0)
-- --   field Ctx : Param -> 𝒰 (𝑗 ⌄ 1)
-- --   field Type : Param -> 𝒰 (𝑗 ⌄ 2)
-- --   field Term : {a : Param} -> Ctx a -> Type a -> 𝒰 (𝑗 ⌄ 3)

-- -- open isSTT {{...}} public

-- -- record isSTT {𝑗 : 𝔏 ^ 3} {𝑖} (Param : 𝒰 𝑖) : 𝒰 (𝑖 , 𝑗 ⁺) where
-- --   field Ctx : Param -> 𝒰 (𝑗 ⌄ 0)
-- --   field Type : Param -> 𝒰 (𝑗 ⌄ 1)
-- --   field Term : {a : Param} -> Ctx a -> Type a -> 𝒰 (𝑗 ⌄ 2)

-- -- open isSTT {{...}} public

-- {-
-- record isSTT {𝑗 : 𝔏 ^ 4} {𝑖} (Theory : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
--   field Param : Theory -> 𝒰 (𝑗 ⌄ 0)
--   field Ctx : ∀{𝒯 : Theory} -> Param 𝒯 -> 𝒰 (𝑗 ⌄ 1)
--   field Type : ∀{𝒯 : Theory} -> Param 𝒯 -> 𝒰 (𝑗 ⌄ 2)
--   field Term : ∀{𝒯 : Theory} -> {a : Param 𝒯} -> Ctx a -> Type a -> 𝒰 (𝑗 ⌄ 3)


-- open isSTT {{...}} public

-- module _ {Theory : 𝒰 𝑖} {{_ : isSTT {𝑗} Theory}} where
--   Ctx' : (𝒯 : Theory) -> Param 𝒯 -> 𝒰 _
--   Ctx' 𝒯 a = Ctx {𝒯 = 𝒯} a

--   syntax Ctx' 𝒯 a = Ctx a of 𝒯


-- -}

-- -- SMTT : STT

-- -- let 𝒯 : SMTT, Γ : Ctx a of 𝒯  , t : 𝒯 , Γ ⊢ A of 𝒯




