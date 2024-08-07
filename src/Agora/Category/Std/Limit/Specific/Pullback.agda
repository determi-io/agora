-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Category.Std.Limit.Specific.Pullback where

open import Agora.Conventions
open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition



module _ {𝒞 : Category 𝑖} where

  record PullbackData : 𝒰 𝑖 where
    constructor _,_
    field {source₀} {source₁} {target} : ⟨ 𝒞 ⟩
    field map₀ : source₀ ⟶ target
    field map₁ : source₁ ⟶ target

  open PullbackData public

  record isPullbackCandidate (𝒹 : PullbackData) (x : Obj 𝒞) : 𝒰 𝑖 where
    constructor is-PullbackCandidate
    field π₀-Pb : ⟨ x ⟩ ⟶ 𝒹 .source₀
    field π₁-Pb : ⟨ x ⟩ ⟶ 𝒹 .source₁
    field ∼-Pb : π₀-Pb ◆ 𝒹 .map₀ ∼ π₁-Pb ◆ 𝒹 .map₁

  open isPullbackCandidate {{...}} public

  PullbackCandidate : ∀ (𝒹 : PullbackData) -> 𝒰 _
  PullbackCandidate 𝒹 = _ :& isPullbackCandidate 𝒹

  record isPullback {𝒹 : PullbackData} (c : PullbackCandidate 𝒹) : 𝒰 𝑖 where
    constructor is-pullback
    field intro-Pb : ∀{d : PullbackCandidate 𝒹} -> ⟨ d ⟩ ⟶ ⟨ c ⟩
    -- field unique-Pb : ∀{d : PullbackCandidate 𝒹} -> ∀{f : ⟨ d ⟩ ⟶ ⟨ c ⟩} -> f ∼ intro-Pb


module _ {𝒞 : Category 𝑖} where
  pb₀ : ∀{𝒹 : PullbackData {𝒞 = 𝒞}} -> (x : PullbackCandidate 𝒹) -> _
  pb₀ X = π₁-Pb {{of X}}

module _ (𝒞 : Category 𝑖) where
  hasPullback : PullbackData {𝒞 = 𝒞} -> _
  hasPullback 𝒹 = _ :& isPullback {𝒹 = 𝒹}

record hasPullbacks (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  constructor has-Pullbacks
  field pullback : ∀{a b c : ⟨ 𝒞 ⟩} -> (f : a ⟶ c) -> (g : b ⟶ c) -> PullbackCandidate {𝒞 = 𝒞} (f , g)
  field isPullback:pullback : ∀{a b c : ⟨ 𝒞 ⟩} -> {f : a ⟶ c} -> {g : b ⟶ c}
                              -> isPullback (pullback f g)

  _◰_ : ∀{a b c : ⟨ 𝒞 ⟩} -> (f : a ⟶ c) -> (g : b ⟶ c) -> ⟨ 𝒞 ⟩
  _◰_ f g = ⟨ pullback f g ⟩



  -- record isCoequalizer {a b : X} (f g : a ⟶ b) (x : X) : 𝒰 (𝑖 ､ 𝑗) where
  --   field π-Coeq : b ⟶ x
  --         ∼-Coeq : f ◆ π-Coeq ∼ g ◆ π-Coeq
  --         elim-Coeq : ∀{c : X} -> (h : b ⟶ c) -> (f ◆ h ∼ g ◆ h) -> x ⟶ c
  --         reduce-Coeq : ∀{c : X} -> (h : b ⟶ c) -> (p : f ◆ h ∼ g ◆ h)
  --                       -> π-Coeq ◆ elim-Coeq h p ∼ h
  --         expand-Coeq : ∀{c : X} -> (h : x ⟶ c) -> (p : f ◆ (π-Coeq ◆ h) ∼ g ◆ (π-Coeq ◆ h)) -> h ∼ elim-Coeq (π-Coeq ◆ h) p
  --         -- (assoc-r-◆ ∙ (∼-Coeq ◈ refl) ∙ assoc-l-◆)

  -- open isCoequalizer {{...}} public


