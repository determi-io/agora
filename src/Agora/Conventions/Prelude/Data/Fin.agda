-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Conventions.Prelude.Data.Fin where

open import Agora.Conventions.Proprelude
open import Agora.Conventions.Prelude.Classes
open import Agora.Conventions.Prelude.Data.Nat

open import Agora.Conventions.Prelude.Data.FinData.Base public
-- renaming (Fin to Fin-R) public
-- ; toℕ to toℕ-Fin-R ; ¬Fin0 to ¬Fin0-R) public


≤→Fin : ∀{a b} -> {{_ : a ≤-ℕ-Dec b}} -> (Fin-R (suc b))
≤→Fin {a = zero} {{p}} = zero
≤→Fin {a = suc a} {.(suc _)} {{suc {{p}}}} = suc (≤→Fin {{p}})


