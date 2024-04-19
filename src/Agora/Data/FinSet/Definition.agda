-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Data.FinSet.Definition where

open import Agora.Conventions
open import Agora.Data.Product.Definition
open import Agora.Data.Sum.Definition
open import Agora.Data.Fin.Definition

open import Agora.Data.Universe.Instance.Setoid


record isFinite (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field size : ℕ
  field index : A -> Fin size
  field isIso:index : isIso-𝒰 index

open isFinite using (size) public
open isFinite {{...}} using (index ; isIso:index) public


module _ (𝑖 : 𝔏) where
  FinSet = 𝒰 𝑖 :& isFinite
  macro 𝐅𝐢𝐧𝐒𝐞𝐭 = #structureOn FinSet

module _ (A : FinSet 𝑖) (B : FinSet 𝑗) where
  record isFinSetHom (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
    constructor tt
    -- field preserves-index : ∀{a} -> index (f a) ≡ 

  open isFinSetHom public

  FinSetHom = _ :& isFinSetHom


module _ {A : FinSet 𝑖} {B : FinSet 𝑗} where
  record _∼-FinSetHom_ (f g : FinSetHom A B) : 𝒰 (𝑖 ､ 𝑗) where
    constructor incl
    field ⟨_⟩ : ∀ a -> ⟨ f ⟩ a ≡ ⟨ g ⟩ a

  open _∼-FinSetHom_ public

  instance
    isEquivRel:∼-FinSetHom : isEquivRel _∼-FinSetHom_
    isEquivRel:∼-FinSetHom = record { refl-∼ = incl λ _ -> refl-≡ ; sym = {!!} ; _∙_ = {!!} }

  instance
    isSetoid:FinSetHom : isSetoid (FinSetHom A B)
    isSetoid:FinSetHom = record { _∼_ = _∼-FinSetHom_ }


id-𝐅𝐢𝐧𝐒𝐞𝐭 : ∀{A : 𝐅𝐢𝐧𝐒𝐞𝐭 𝑖} -> FinSetHom A A
id-𝐅𝐢𝐧𝐒𝐞𝐭 =  (λ a -> a) since tt

_◆-𝐅𝐢𝐧𝐒𝐞𝐭_ : {A : 𝐅𝐢𝐧𝐒𝐞𝐭 𝑖} {B : 𝐅𝐢𝐧𝐒𝐞𝐭 𝑗} {C : 𝐅𝐢𝐧𝐒𝐞𝐭 𝑘} -> FinSetHom A B -> FinSetHom B C -> FinSetHom A C
_◆-𝐅𝐢𝐧𝐒𝐞𝐭_ f g = (λ x -> ⟨ g ⟩ (⟨ f ⟩ x)) since tt


open import Agora.Category.Std.Category.Definition

instance
  isCategoryData:𝐅𝐢𝐧𝐒𝐞𝐭 : isCategoryData (𝐅𝐢𝐧𝐒𝐞𝐭 𝑖) FinSetHom
  isCategoryData:𝐅𝐢𝐧𝐒𝐞𝐭 = record
                           { isSetoid:Hom = isSetoid:FinSetHom
                           ; id = id-𝐅𝐢𝐧𝐒𝐞𝐭
                           ; _◆_ = _◆-𝐅𝐢𝐧𝐒𝐞𝐭_
                           ; unit-l-◆ = incl (incl λ a -> refl-≡)
                           ; unit-r-◆ = incl (incl λ a -> refl-≡)
                           ; unit-2-◆ = incl (incl λ a -> refl-≡)
                           ; assoc-l-◆ = incl (incl λ a -> refl-≡)
                           ; assoc-r-◆ = incl (incl λ a -> refl-≡)
                           ; _◈_ = {!!}
                           }



