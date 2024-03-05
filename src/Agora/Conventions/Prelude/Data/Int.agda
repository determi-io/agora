-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

-- {-# OPTIONS --cubical --allow-unsolved-metas #-}

module Agora.Conventions.Prelude.Data.Int where

open import Agora.Conventions.Prelude.Data.Int.Base public
open import Agora.Conventions.Prelude.Data.Int.Properties renaming (_+_ to _+-ℤ_ ; _-_ to _-ℤ_ ; +-assoc to assoc-+-ℤ ; +-comm to comm-+-ℤ) public

-- open import Cubical.Data.Int renaming (Int to ℤ ; _+_ to _+-ℤ_ ; _-_ to _-ℤ_ ; +-assoc to assoc-+-ℤ ; +-comm to comm-+-ℤ) public

