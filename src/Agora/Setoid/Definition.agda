
module Agora.Setoid.Definition where

open import Agora.Conventions
open import Agora.Data.Prop.Definition
open import Agora.Data.Product.Definition


-- record ∼-Base {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) (a : A) (b : A) : 𝒰 (𝑗) where
--   constructor incl
--   field ⟨_⟩ : R a b
--   -- incl : R a b -> ∼-Base R a b -- a ∼[ R ] b
-- open ∼-Base public

-- module _ {A : 𝒰 𝑖} {{S : isSetoid {𝑗} A}} where
-- --   -- private instance _ = S

--   isSetoid:∼-Base : isSetoid A
--   isSetoid:∼-Base = isSetoid:byDef
--     (∼-Base (_∼_))
--     (incl (refl))
--     (λ p -> incl (sym ⟨ p ⟩))
--     (λ p q -> incl (⟨ p ⟩ ∙ ⟨ q ⟩))


Setoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Setoid 𝑗 = 𝒰 (𝑗 ⌄ 0) :& isSetoid {𝑗 ⌄ 1}

-- refl2 : ∀{A : 𝒰 𝑖} -> {P : A -> A -> 𝒰 𝑗}
--         -> {a : A}
--         -> {{S : isSetoid {𝑗} A}}
--         -> {{_ : _∼_ {{S}} ≡ P}}
--         -> P a a
-- refl2 {{S}} {{refl-≡}} = refl


-- Of : ∀(A : 𝒰 𝑖) -> A -> A
-- Of _ a = a



-- module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isDefault A}} {{_ : isDefault B}} where
  -- instance
  --   isDefault:× : isDefault (A ×-𝒰 B)
  --   isDefault:× = {!!}

  -- aD : ∀{A B : 𝒰 𝑖} -> {{_ : isDefault A}} -> {{_ : isDefault B}} -> isDefault (A ×-𝒰 B)
  -- aD = {!!}

-- mytest2 : ∀{A B : 𝒰 𝑖} -> (A : _ :& isDefault {𝑖 = 𝑖}) -> (B : _ :& isDefault {𝑖 = 𝑖}) -> (a : ⟨ A ⟩) -> myProp a a
-- mytest2 X P a = valp


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isSetoid {𝑖₁} A}} {{_ : isSetoid {𝑗₁} B}} where
  _∼-×_ : (A × B) -> (A × B) -> 𝒰 _
  (a₀ , b₀) ∼-× (a₁ , b₁) = (a₀ ∼ a₁) × (b₀ ∼ b₁)

  instance
    isEquivRel:∼-× : isEquivRel _∼-×_
    isEquivRel:∼-× = record
      { refl = (refl , refl)
      ; sym = (λ (p , q) -> (p ⁻¹ , q ⁻¹))
      ; _∙_ = (λ (p₀ , q₀) (p₁ , q₁) -> (p₀ ∙ p₁ , q₀ ∙ q₁))
      }

    isSetoid:× : isSetoid (A ×-𝒰 B)
    isSetoid:× = record { _∼_ = _∼-×_ }

-- instance
--   isEquivRel:≡∼-Base : ∀{A : 𝒰 𝑖} -> isEquivRel (∼-Base (_≡_ {A = A}))
--   isEquivRel.refl isEquivRel:≡∼-Base = incl refl-Path
--   isEquivRel.sym isEquivRel:≡∼-Base (incl p) = incl (sym-Path p)
--   isEquivRel._∙_ isEquivRel:≡∼-Base (incl p) (incl q) = incl (trans-Path p q)

-- instance
--   isEquivRel:≡∼-Base : ∀{A : 𝒰 𝑖} -> isEquivRel (∼-Base (_≡_ {A = A}))
--   isEquivRel.refl isEquivRel:≡∼-Base = incl refl-StrId
--   isEquivRel.sym isEquivRel:≡∼-Base (incl p) = incl (p ⁻¹)
--   isEquivRel._∙_ isEquivRel:≡∼-Base (incl p) (incl q) = incl (p ∙ q)

-- record isSetoid 𝑗 A {{_ : From (𝒰 𝑖) A}} : 𝒰 (𝑖 ､ 𝑗 ⁺) where
-- open isTypoid {{...}} public


{-
record isSetoid {𝑗 𝑖 : 𝔏} (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  constructor setoid
  field _∼_ : A -> A -> 𝒰 𝑗
        refl : ∀{x : A} -> x ∼ x
        sym : ∀{x y : A} -> x ∼ y -> y ∼ x
        _∙_ : ∀{x y z : A} -> x ∼ y -> y ∼ z -> x ∼ z

  infixl 30 _∙_

  -- _∼_ : A -> A -> 𝒰 (𝑗)
  -- _∼_ = ∼-Base _∼'_

  -- field {{isEquivRel:∼}} : isEquivRel _∼_

  _≁_ : A -> A -> 𝒰 (𝑗)
  _≁_ a b = ¬ a ∼ b
open isSetoid {{...}} public

module _ {X : 𝒰 _} {{_ : X is Setoid 𝑖}} where
  instance
    Notation-Inverse:Equiv : {x y : X} -> Notation-Inverse (x ∼ y) (y ∼ x)
    Notation-Inverse:Equiv Notation-Inverse.⁻¹ = sym

-}



-- record isSetoidHom {𝑖 𝑗 : 𝔏 ^ 2} {A : 𝒰 _} {B : 𝒰 _} {{_ : Setoid 𝑖 on A}} {{_ : Setoid 𝑗 on B}} (f : A -> B) : 𝒰 (𝑖 ､ 𝑗)where

record isSetoidHom {𝑖 𝑗 : 𝔏 ^ 2} (A : Setoid 𝑖) (B : Setoid 𝑗) (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
  field cong-∼ : ∀{a b} -> a ∼ b -> f a ∼ f b
open isSetoidHom {{...}} public


SetoidHom : (A : Setoid 𝑖) (B : Setoid 𝑗) -> 𝒰 _
SetoidHom A B = (⟨ A ⟩ -> ⟨ B ⟩) :& isSetoidHom A B

module _ {A : Setoid 𝑖} {B : Setoid 𝑗} where
  congOf-∼ : (f : SetoidHom A B) -> ∀{a b : ⟨ A ⟩} -> a ∼ b -> ⟨ f ⟩ a ∼ ⟨ f ⟩ b
  congOf-∼ f = cong-∼

  infixl 200 _-cong-∼_
  _-cong-∼_ = congOf-∼



-- module _ {A : 𝒰 𝑖} {{_ : isDefault A}} {B : 𝒰 𝑗} {{_ : isDefault B}} where
--   myprop : ∀{f : A -> B} -> ∀{a} -> myProp (f a) (f a)
--   myprop {f} {a} = {!valp!}

-- module _ {A : 𝒰 𝑖} {{_ : isSetoid {𝑖₁} A}} {B : 𝒰 𝑗} {{_ : isSetoid {𝑗₁} B}} where

module _ {A : Setoid 𝑖} {B : Setoid 𝑗} where
  _∼-SetoidHom_ : (f g : SetoidHom A B) -> 𝒰 _
  _∼-SetoidHom_ f g = ∀{a} -> ⟨ f ⟩ a ∼ ⟨ g ⟩ a

  instance
    isEquivRel:∼-SetoidHom : isEquivRel _∼-SetoidHom_
    isEquivRel:∼-SetoidHom = record
      { refl = refl
      ; sym = (λ p -> sym p)
      ; _∙_ = (λ p q -> p ∙ q)
      }

  instance
    isSetoid:SetoidHom : isSetoid (SetoidHom A B)
    isSetoid:SetoidHom = record { _∼_ = _∼-SetoidHom_ }


{-

{-
module _ {A : Setoid 𝑖} {B : Setoid 𝑗} where
  _∼-SetoidHom_ : (f g : SetoidHom A B) -> 𝒰 _
  _∼-SetoidHom_ f g = ∀{a} -> ⟨ f ⟩ a ∼ ⟨ g ⟩ a

  instance
    isEquivRel:∼-SetoidHom : isEquivRel (∼-Base _∼-SetoidHom_)
    isEquivRel.refl isEquivRel:∼-SetoidHom = incl (λ {a} → refl)
    isEquivRel.sym isEquivRel:∼-SetoidHom (incl p) = incl (p ⁻¹)
    isEquivRel._∙_ isEquivRel:∼-SetoidHom (incl p) (incl q) = incl (p ∙ q)

  instance
    isSetoid:SetoidHom : isSetoid _ (SetoidHom A B)
    isSetoid._∼'_ isSetoid:SetoidHom = _∼-SetoidHom_


instance
  isSetoid:⦋𝒫⦌ : ∀{𝑖 𝑗 : 𝔏} {A : 𝒰 𝑖} -> {{_ : isSetoid 𝑗 A}} -> {P : 𝒫 A} -> isSetoid _ ⦋ P ⦌
  isSetoid._∼'_ isSetoid:⦋𝒫⦌ (a ∢ _) (b ∢ _) = a ∼ b
  isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:⦋𝒫⦌) {x = a ∢ x} = incl refl
  isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:⦋𝒫⦌) {a ∢ x} {a₁ ∢ x₁} (incl p) = incl (sym p)
  isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:⦋𝒫⦌) {a ∢ x} {a₁ ∢ x₁} {a₂ ∢ x₂} (incl p) (incl q) = incl (p ∙ q)


-------------------------------------------------------------------------------
-- inheriting setoid structures

-}
module _ {UU : 𝒰 𝑖} {{U : hasU UU 𝑗 𝑘}} {{_ : isSetoid {𝑙} (getU U)}} where
  _∼-hasU_ : UU -> UU -> 𝒰 _
  _∼-hasU_ a b = destructEl U a ∼ destructEl U b

  -- isEquivRel:hasU : isEquivRel (∼-Base _∼-hasU_)
  -- isEquivRel.refl isEquivRel:hasU = incl ⟨ refl ⟩
  -- isEquivRel.sym isEquivRel:hasU (incl p) = incl (⟨ sym (incl p) ⟩)
  -- isEquivRel._∙_ isEquivRel:hasU (incl p) (incl q) = incl ⟨ ((incl p) ∙ (incl q)) ⟩

  isSetoid:hasU : isSetoid UU
  isSetoid._∼_ isSetoid:hasU = ∼-Base _∼-hasU_
  isSetoid.refl isSetoid:hasU = incl refl
  isSetoid.sym isSetoid:hasU = λ p -> incl (sym ⟨ p ⟩)
  isSetoid._∙_ isSetoid:hasU = λ p q -> incl ( ⟨ p ⟩ ∙ ⟨ q ⟩ )
  -- isSetoid._∼'_ isSetoid:hasU = _∼-hasU_
  -- isSetoid.isEquivRel:∼ isSetoid:hasU = isEquivRel:hasU



--------------------------------------------------------------------------------
-- Subsetoids




--
-- NOTE: We (probably) use the instance argument form of passing the setoid structure here,
--       such that we can state `isSubsetoid P` instead of saying `isSubsetoid X P`.
--
--       The same pattern is used for submonoid, etc. in Core/Algebra.
--
--       The alternative, that we don't use, would be:
--       '''
--       record isSubsetoid {𝑗 : 𝔏 ^ 2} (X : Setoid 𝑗) (P : 𝒫 ⟨ X ⟩) : 𝒰 𝑗 where
--       '''
--
record isSubsetoid {𝑗 : 𝔏 ^ 2} {X : 𝒰' _} {{_ : Setoid 𝑗 on X}} (P : X -> Prop (𝑗 ⌄ 0)) : 𝒰 𝑗 where
  field transp-∼ : ∀{a b : X} -> a ∼ b -> a ∈ P -> b ∈ P

open isSubsetoid {{...}} public

Subsetoid : {𝑗 : 𝔏 ^ 2} (X : Setoid 𝑗) -> 𝒰 _
Subsetoid X = 𝒫-𝒰 ⟨ X ⟩ :& isSubsetoid

module _ {X : 𝒰' _} {{SX : Setoid 𝑗 on X}} where
  transpOf-∼ : (V : Subsetoid ′ X ′) -> ∀{a b : X} -> a ∼ b -> a ∈ V -> b ∈ V
  transpOf-∼ V a∼b a∈V = transp-∼ a∼b a∈V


---------------------------------------------------------------
-- induced subsetoid


isSetoid:FullSubsetoid : (X : Setoid 𝑖) {A : 𝒰 𝑗} (ϕ : A -> ⟨ X ⟩) -> isSetoid A
isSetoid:FullSubsetoid X ϕ = isSetoid:byDef (∼-Base (λ a b -> ϕ a ∼ ϕ b))
  (incl refl)
  (λ p -> incl (sym ⟨ p ⟩))
  (λ p q -> incl (⟨ p ⟩ ∙ ⟨ q ⟩))

-- isSetoid._∼'_ (isSetoid:FullSubsetoid X ϕ) = λ a b -> ϕ a ∼ ϕ b
-- isSetoid.isEquivRel:∼ (isSetoid:FullSubsetoid X ϕ) = equivRel (incl refl) (λ p -> incl (sym ⟨ p ⟩)) (λ p q -> incl (⟨ p ⟩ ∙ ⟨ q ⟩))

isContr-Std : (A : 𝒰 _) {{_ : Setoid 𝑖 on A}} -> 𝒰 _
isContr-Std A = ∑ λ (a : A) -> ∀ (b : A) -> a ∼ b


{-

-- instance
--   isEquivRel:⫗ : ∀{A : 𝒰 𝑖} -> isEquivRel (∼-Base (λ (P Q : A -> 𝒰 𝑗) -> P ⫗ Q))
--   isEquivRel.refl isEquivRel:⫗ = incl ((λ x -> x) , (λ x -> x))
--   isEquivRel.sym isEquivRel:⫗ (incl (P , Q)) = incl (Q , P)
--   isEquivRel._∙_ isEquivRel:⫗ (incl (P₀ , Q₀)) (incl (P₁ , Q₁)) = incl ((λ x -> P₁ (P₀ x)) , (λ x -> Q₀ (Q₁ x)))

-- instance
--   isEquivRel:⫗ : ∀{𝑖 : 𝔏 ^ 2} -> ∀{A : Setoid 𝑖} -> isEquivRel (∼-Base (λ (P Q : Subsetoid A) -> ⟨ P ⟩ ⫗ ⟨ Q ⟩))
--   isEquivRel.refl isEquivRel:⫗ = incl ((λ x -> x) , (λ x -> x))
--   isEquivRel.sym isEquivRel:⫗ (incl (P , Q)) = incl (Q , P)
--   isEquivRel._∙_ isEquivRel:⫗ (incl (P₀ , Q₀)) (incl (P₁ , Q₁)) = incl ((λ x -> P₁ (P₀ x)) , (λ x -> Q₀ (Q₁ x)))

-- instance
--   isSetoid:Subsetoid : ∀{𝑗 : 𝔏 ^ 2} -> {X : Setoid 𝑗} -> isSetoid _ (Subsetoid X)
--   isSetoid._∼'_ isSetoid:Subsetoid A B = ⟨ A ⟩ ⫗ ⟨ B ⟩

--------------------------------------------------------------------------------
-- Quotients
-}

data _/-𝒰_ {𝑖 𝑗 : 𝔏} (A : 𝒰 𝑖) (R : A -> A -> 𝒰 𝑗) : 𝒰 (𝑖 ) where
  [_] : A -> A /-𝒰 R

-- private
--   module _ {𝑖 𝑘 : 𝔏} {A : 𝒰 𝑖} -> {R : A -> A -> 𝒰 𝑘} -> {{_ : isEquivRel R}} where
--     lem-10 : ∀{a : A /-𝒰 R} -> 



instance
  isSetoid:/-𝒰 : {𝑖 𝑘 : 𝔏} {A : 𝒰 𝑖} -> {R : A -> A -> 𝒰 𝑘} -> {{_ : isEquivRel R}} -> isSetoid (A /-𝒰 R)
  isSetoid._∼_ (isSetoid:/-𝒰 {R = R}) = ∼-Base (λ {[ a ] [ b ] -> R a b}) -- λ {[ a ] [ b ] -> ∼-Base R a b}
  isSetoid.refl (isSetoid:/-𝒰 {R = R}) {[ x ]} = incl refl-Equiv
  isSetoid.sym (isSetoid:/-𝒰 {R = R}) {[ x ]} {[ y ]} (incl p) = incl (sym-Equiv p)
  isSetoid._∙_ (isSetoid:/-𝒰 {R = R}) {[ x ]} {[ y ]} {[ z ]} (incl p) (incl q) = incl (p ∙-Equiv q)
  -- setoid (λ {[ a ] [ b ] -> ∼-Base R a b})
  --                        (λ {x} → {!!})
  --                        {!!}
  --                        {!!}
    -- (λ {[ x ]} -> refl-Equiv)
    -- {!!} {!!}
  -- isSetoid._∼'_ (isSetoid:/-𝒰 {R = R}) [ a ] [ b ] = R a b
  -- isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} = incl refl-Equiv
  -- isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} {y = [ y ]} (incl p) = incl (sym-Equiv p)
  -- isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:/-𝒰) {x = [ x ]} {y = [ y ]} {z = [ z ]} (incl p) (incl q) = incl (p ∙-Equiv q)

--------------------------------------------------------------------------------
-- Induced setoid

-}


-- macro
--   _×_ : ∀{𝑖 𝑗 : 𝔏} {𝑘 𝑙 : 𝔏 ^ 2} -> (𝒰' 𝑖) [ 𝑙 ]→ (𝒰' 𝑗) [ 𝑘 ]→ SomeStructure
--   _×_ = λstr A ↦ λstr B ↦ #structureOn (A ×-𝒰 B)
--   infixr 40 _×_

macro
  _→#_ : ∀{𝑗 : 𝔏} {𝑘 : 𝔏 ^ 2} -> (I : 𝒰 𝑖) -> (𝒰' 𝑗) [ 𝑘 ]→ SomeStructure
  _→#_ I = λstr A ↦ #structureOn (I -> A)



module _ {A : 𝒰 𝑖} {{S : isSetoid {𝑗} A}} {I : 𝒰 𝑘} where
  _∼-Family_ : (f g : I -> A) -> 𝒰 _
  _∼-Family_ f g = ∀ i -> f i ∼ g i

  -- instance
  --   isEquivRel:∼-Family : isEquivRel (∼-Base _∼-Family_)
  --   isEquivRel.refl isEquivRel:∼-Family {f} = incl (λ {a} -> ⟨ refl {a = f a} ⟩)
  --   isEquivRel.sym isEquivRel:∼-Family (incl p) = incl (⟨ incl p ⁻¹ ⟩)
  --   isEquivRel._∙_ isEquivRel:∼-Family (incl p) (incl q) = incl (⟨ incl p ∙ incl q ⟩)

  instance
    isEquivRel:∼-Family : isEquivRel _∼-Family_
    isEquivRel:∼-Family = record
      { refl = (λ i -> refl)
      ; sym = (λ p i -> sym (p i))
      ; _∙_ = (λ p q i -> (p i) ∙ (q i))
      }

  instance
    isSetoid:Family : isSetoid (I -> A)
    isSetoid:Family = record { _∼_ = _∼-Family_ }

    -- isSetoid._∼'_ isSetoid:Family f g = f ∼-Family g

    -- isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:Family) = incl (⟨ refl ⟩)
    -- isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:Family) (incl p) = incl (⟨ incl p ⁻¹ ⟩)
    -- isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:Family) (incl p) (incl q) = incl (⟨ incl p ∙ incl q ⟩)

-------------------------------------------------------------------------------
-- Isomorphism of setoids

