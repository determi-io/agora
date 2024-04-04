
module Agora.Category.Std.Fibration.Instance.BaseChange where

open import Agora.Conventions

-- open import Agora.Setoid.Definition
-- open import Agora.Set.Set.Definition
-- open import Agora.Set.Set.Instance.Category
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Functor.Definition
-- open import Agora.Category.Std.Category.Opposite
-- open import Agora.Category.Std.Morphism.Iso
-- open import Agora.Category.Std.Category.Instance.Category
-- open import Agora.Category.Std.Limit.Specific.Pullback

-- open import Agora.Data.Universe.Definition
-- open import Agora.Data.Universe.Definition
open import Agora.Data.Universe.Instance.Category


open import Agora.Category.Std.Fibration.BaseChange.Definition
open import Agora.Category.Std.Fibration.Definition


module _ {ℰ : Category 𝑖} {ℬ : Category 𝑗} (p : Fibration ℰ ℬ) where

  hasBaseChange:Fibration : hasBaseChange _ ℬ
  hasBaseChange:Fibration = basechange (FiberF p) {!!} {!!}



