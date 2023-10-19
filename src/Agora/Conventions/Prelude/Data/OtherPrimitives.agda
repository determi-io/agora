

module Agora.Conventions.Prelude.Data.OtherPrimitives where

open import Agora.Conventions.Proprelude
open import Agora.Conventions.Prelude.Classes
open import Agora.Conventions.Prelude.Data.Nat

open import Agda.Builtin.Word
open import Agda.Builtin.Float

instance
  IBootEq:Word64 : IBootEq Word64
  IBootEq._≟_ IBootEq:Word64 a b = primWord64ToNat a ≟ primWord64ToNat b

  IBootEq:Float : IBootEq Float
  IBootEq._≟_ IBootEq:Float  = primFloatEquality
