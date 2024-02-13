
module Agora.Data.List.Definition where

open import Agora.Conventions

open import Agora.System.Marshall.Data.DecidableEquality

open import Data.List using (List)
open import Data.List.Properties using () renaming (≡-dec to ≡-dec-List-Std)

module _ {A : 𝒰 𝑖} {{_ : hasDecidableEquality A}} where
  _≟-List_ : (k l : List A) -> isDecidable (k ≡ l)
  _≟-List_ k l = cast-Dec-Std (≡-dec-List-Std (λ a b -> cast⁻¹-Dec-Std (a ≟ b)) k l)

  instance
    hasDecidableEquality:List : hasDecidableEquality (List A)
    hasDecidableEquality:List = record { _≟_ = _≟-List_ }


