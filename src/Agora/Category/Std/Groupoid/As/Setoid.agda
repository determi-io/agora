
module Agora.Category.Std.Groupoid.As.Setoid where

open import Agora.Conventions

open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Groupoid.Definition

GroupoidAsSetoid : Groupoid 𝑖 -> Setoid _
GroupoidAsSetoid 𝒢 = ⟨ 𝒢 ⟩ since isSetoid:byDef (λ a b -> a ⟶ b) id _⁻¹-𝐆𝐫𝐩𝐝 _◆_



