-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

module Agora.Conventions.Proprelude.Equality.Cubical where


-- id-Path : ∀{A : 𝒰 𝑖} -> {a : A} -> a ≡ a
-- id-Path {a = a} = λ _ -> a

-- module _ {A : 𝒰 𝑖} where
--   funExt⁻¹ : {B : A → I → 𝒰 ℓ'}
--     {f : (x : A) → B x i0} {g : (x : A) → B x i1}
--     → PathP (λ i → (x : A) → B x i) f g
--     → ((x : A) → PathP (B x) (f x) (g x))
--   funExt⁻¹ p x i = p i x


-- cong₂ : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} -> (f : A -> B -> C) -> {a1 a2 : A} -> {b1 b2 : B} -> (p : a1 ≡ a2) -> (q : b1 ≡ b2) -> f a1 b1 ≡ f a2 b2
-- cong₂ f p q i = f (p i) (q i)


-- infixr 30 _×-𝒰_
-- _×-𝒰_ : 𝒰 ℓ -> 𝒰 ℓ' -> 𝒰 (ℓ ⊔ ℓ')
-- A ×-𝒰 B = ∑ λ (a : A) -> B


