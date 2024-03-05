-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.System.Marshall.Data.DecidableEquality where

-- Converting between various definitions of decidable equality

open import Agora.Conventions

-- open import Prelude.Equality using (Eq)
-- open import Prelude.Decidable using () renaming (Dec to Dec-Prelude)
-- open import Prelude.Empty using () renaming (⊥-elim to ⊥-elim-Prelude)


open import Relation.Nullary.Decidable.Core using () renaming (Dec to Dec-Std ; yes to yes-Std ; no to no-Std)

---------------------------------------------
-- Converting between the Prelude Dec and the Agora Dec

-- cast-Dec-Prelude : ∀{A : 𝒰 𝑖} -> Dec-Prelude A -> isDecidable A
-- cast-Dec-Prelude (Dec-Prelude.yes x) = yes x
-- cast-Dec-Prelude (Dec-Prelude.no x) = no λ x₁ → ⊥-elim-Prelude (x x₁)

-- cast⁻¹-Dec-Prelude : ∀{A : 𝒰 𝑖} -> isDecidable A -> Dec-Prelude A
-- cast⁻¹-Dec-Prelude (yes x) = Dec-Prelude.yes x
-- cast⁻¹-Dec-Prelude (no x) = Dec-Prelude.no λ x₁ → ⊥-elim (x x₁)

cast-Dec-Std : ∀{A : 𝒰 𝑖} -> Dec-Std A -> isDecidable A
cast-Dec-Std (yes-Std a) = yes a
cast-Dec-Std (no-Std a) = no a

cast⁻¹-Dec-Std : ∀{A : 𝒰 𝑖} -> isDecidable A -> Dec-Std A
cast⁻¹-Dec-Std (yes a) = (yes-Std a)
cast⁻¹-Dec-Std (no a)  = (no-Std a)



