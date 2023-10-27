
module Agora.Data.Universe.Instance.Setoid where

--
-- MIGRATION NOTES: ported from `Verification.Core.Data.Universe.Instance.Setoid`
--  - Changed definition of `isIso-𝒰` to use `_≡-Str_` instead of the path types `_≡_`
--  - Commented out the "Coercible" code
--


open import Agora.Conventions

open import Agora.Data.Universe.Definition
-- open import Agora.Data.Product.Definition
-- open import Agora.Data.Universe.Instance.Category using (isSetoid:𝒰) public


record isIso-𝒰 {a : 𝒰 𝑖} {b : 𝒰 𝑗} (f : a -> b) : 𝒰 (𝑖 ､ 𝑗) where
  field inverse-𝒰 : b -> a
        inv-r-◆-𝒰 : ∀ x -> (f ◆-𝒰 inverse-𝒰) x ≡-Str x
        inv-l-◆-𝒰 : ∀ x -> (inverse-𝒰 ◆-𝒰 f) x ≡-Str x
open isIso-𝒰 {{...}} public

_≅-𝒰_ : (A : 𝒰 𝑖) (B : 𝒰 𝑗) -> 𝒰 (𝑖 ､ 𝑗)
A ≅-𝒰 B = (A -> B) :& isIso-𝒰

private
  lem-10 : ∀{A : 𝒰 𝑖} -> isIso-𝒰 (id-𝒰 {A = A})
  isIso-𝒰.inverse-𝒰 lem-10 = id-𝒰
  isIso-𝒰.inv-r-◆-𝒰 lem-10 = λ x → refl-≣ -- refl-≡
  isIso-𝒰.inv-l-◆-𝒰 lem-10 = λ x → refl-≣ -- refl-≡

  lem-20 : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> {f : A ≅-𝒰 B} -> isIso-𝒰 inverse-𝒰
  isIso-𝒰.inverse-𝒰 (lem-20 {f = f}) = ⟨ f ⟩
  isIso-𝒰.inv-r-◆-𝒰 (lem-20 {f = f}) = inv-l-◆-𝒰
  isIso-𝒰.inv-l-◆-𝒰 (lem-20 {f = f}) = inv-r-◆-𝒰

  -- lem-30 : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} -> {f : A ≅-𝒰 B} -> {g : B ≅-𝒰 C} -> isIso-𝒰 (⟨ f ⟩ ◆-𝒰 ⟨ g ⟩)
  -- isIso-𝒰.inverse-𝒰 (lem-30 {f = f}) = inverse-𝒰 ◆-𝒰 inverse-𝒰
  -- isIso-𝒰.inv-r-◆-𝒰 (lem-30 {f = f} {g = g}) = {!λ x -> cong-Str ⟨ f ⟩ (inv-r-◆-𝒰 {{of g}} _) ∙-≣ ?!}
  -- isIso-𝒰.inv-l-◆-𝒰 (lem-30 {f = f}) = {!!}

-- instance
  -- isEquivRel:≅-𝒰 : isEquivRel (∼-Base (_≅-𝒰_ {𝑖} {𝑖}))
  -- isEquivRel:≅-𝒰 = {!!}
  -- isEquivRel.refl isEquivRel:≅-𝒰 = incl (′ id-𝒰 ′ {{lem-10}})
  -- isEquivRel.sym  isEquivRel:≅-𝒰 (incl f) = incl (′ inverse-𝒰 ′ {{lem-20 {f = f}}})
  -- isEquivRel._∙_  isEquivRel:≅-𝒰 (incl f) (incl g) = incl (′ ⟨ f ⟩ ◆-𝒰 ⟨ g ⟩ ′ {{lem-30 {f = f} {g = g}}})

-- instance
--   isSetoid:𝒰 : isSetoid (𝒰 𝑖)
--   isSetoid:𝒰 = isSetoid:byDef
--     _≅-𝒰_
--     (id-𝒰 since lem-10)
--     (λ f -> inverse-𝒰 since lem-20 {f = f})
--     (λ f g -> ⟨ f ⟩ ◆-𝒰 ⟨ g ⟩ since lem-30 {f = f} {g = g})


--------------------------------------------------
-- We allow for coercion when types are isomorphic

-- record isCoercible (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
--   constructor introCoercible
--   field coeIso : A ≅-𝒰 B


-- open isCoercible public

-- module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
--   coe : {{isCoercible A B}} -> A -> B
--   coe {{P}} = ⟨ coeIso P ⟩

-- module _ (A : 𝒰 𝑖) (B : 𝒰 𝑗) where
--   Bicoercible = isCoercible A B ×-AgdaInstance isCoercible B A

-- module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
--   introBicoercible : (A ≅-𝒰 B) -> Bicoercible A B
--   introBicoercible ϕ = intro-×-AgdaInstance {{introCoercible ϕ}} {{introCoercible (inverse-𝒰 {{of ϕ}} since lem-20 {f = ϕ})}}



