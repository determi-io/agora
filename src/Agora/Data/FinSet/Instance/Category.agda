-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas #-}

module Agora.Data.FinSet.Instance.Category where

open import Agora.Conventions
open import Agora.Data.Product.Definition
open import Agora.Data.Sum.Definition
open import Agora.Data.Fin.Definition
open import Agora.Data.Universe.Instance.Setoid

open import Agora.Data.FinSet.Definition


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

  sym-∼-FinSetHom : ∀{f g : FinSetHom A B} -> f ∼-FinSetHom g -> g ∼-FinSetHom f
  sym-∼-FinSetHom {f} {g} p = incl (λ a → sym-≡ (⟨ p ⟩ a))

  trans-∼-FinSetHom : ∀{f g h : FinSetHom A B} -> f ∼-FinSetHom g -> g ∼-FinSetHom h -> f ∼-FinSetHom h
  trans-∼-FinSetHom {f} {g} p q = incl (λ a → (⟨ p ⟩ a) ∙-≡ (⟨ q ⟩ a))

  instance
    isEquivRel:∼-FinSetHom : isEquivRel _∼-FinSetHom_
    isEquivRel:∼-FinSetHom = record { refl-∼ = incl λ _ -> refl-≡ ; sym = sym-∼-FinSetHom ; _∙_ = trans-∼-FinSetHom }

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
                           ; _◈_ = λ p q -> incl (incl (λ a₁ → {!!}))
                           }

instance
  isCategory:𝐅𝐢𝐧𝐒𝐞𝐭 : isCategory (𝐅𝐢𝐧𝐒𝐞𝐭 𝑖)
  isCategory:𝐅𝐢𝐧𝐒𝐞𝐭 = record { Hom = FinSetHom }




