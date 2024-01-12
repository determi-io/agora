
-- {-# OPTIONS --lossy-unification #-}

module Agora.Order.Preorder where

open import Agora.Conventions
-- open import Agora.Category.Definition
-- open import Agora.Category.Instance.Set.Definition
-- open import Agora.Type
open import Agora.Setoid.Definition
open import Agora.Data.Universe.Definition

--------------------------------------------------------------------
-- == Preorder

-- record ≤-Base {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) (a b : A) : 𝒰 𝑗 where
--   constructor incl
--   field ⟨_⟩ : (R a b)
-- open ≤-Base public

record isPreorderData (A : 𝒰 𝑖 :& isSetoid {𝑗}) (_≤_ : ⟨ A ⟩ -> ⟨ A ⟩ -> 𝒰 𝑘) : 𝒰 (𝑘 ⁺ ､ 𝑗 ､ 𝑖) where
  field reflexive : {a : ⟨ A ⟩} -> a ≤ a
        _⟡_ : {a b c : ⟨ A ⟩} -> a ≤ b -> b ≤ c -> a ≤ c
        transp-≤ : ∀{a₀ a₁ b₀ b₁ : ⟨ A ⟩} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ ≤ b₀ -> a₁ ≤ b₁

  infixl 40 _⟡_

open isPreorderData {{...}} public


record isPreorder 𝑘 (A : 𝒰 𝑖 :& isSetoid {𝑗}) : 𝒰 (𝑘 ⁺ ､ 𝑗 ､ 𝑖) where
  constructor isPreorder:byDef
  field _≤_ : ⟨ A ⟩ -> ⟨ A ⟩ -> 𝒰 𝑘
  field {{isPreorderData:≤}} : isPreorderData A _≤_

  infixl 40 _≤_

open isPreorder {{...}} public

Preorder : ∀ (𝑖 : 𝔏 ^ 3) -> 𝒰 (𝑖 ⁺)
Preorder 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isSetoid {𝑖 ⌄ 1} :& isPreorder (𝑖 ⌄ 2)

module _ {𝑖 : 𝔏 ^ 3} {A : 𝒰 _} {{_ : Preorder 𝑖 on A}} where
  _≰_ : A -> A -> 𝒰 _
  a ≰ b = ¬ a ≤ b

  _⋦_ : A -> A -> 𝒰 _
  a ⋦ b = (a ≤ b) ×-𝒰 (a ≁ b)

  -- ⋧

--------------------------------------------------------------------
-- == Partial order

module _ {𝑖 : 𝔏 ^ 3} where
  record isPartialorder (A : Preorder 𝑖) : 𝒰 𝑖 where
   field antisym : ∀{a b : ⟨ A ⟩} -> (a ≤ b) -> (b ≤ a) -> a ∼ b
open isPartialorder {{...}} public

Partialorder : (𝑖 : 𝔏 ^ 3) -> 𝒰 _
Partialorder 𝑖 = Preorder 𝑖 :& isPartialorder

----------------------------------------------------------
-- Derived instances


module _ {A : 𝒰 _} {{_ : A is Preorder 𝑗}} {I : 𝒰 𝑙} where

  _≤-Family_ : (I →# A) -> (I →# A) -> 𝒰 _
  _≤-Family_ f g = ∀ a -> f a ≤ g a

  instance
    isPreorderData:≤-Family : isPreorderData (I →# A) _≤-Family_
    isPreorderData:≤-Family = record
      { reflexive = λ a → reflexive
      ; _⟡_ = λ p q a -> p a ⟡ q a
      ; transp-≤ = λ p q f a -> transp-≤ (p a) (q a) (f a)
      }

    isPreorder:≤-Family : isPreorder _ (I →# A )
    isPreorder:≤-Family = record { _≤_ = _≤-Family_ }


-- module _ {A : 𝒰 𝑖} {{_ : isSetoid {𝑗} A}} {{_ : isPreorder 𝑘 ′ A ′}} {{_ : isPartialorder ′ A ′}} where

module _ {A : 𝒰 _} {{_ : A is Partialorder 𝑖}} {I : 𝒰 𝑙} where

  instance
    isPartialorder:Family : isPartialorder (I →# A)
    isPartialorder:Family = record
      { antisym = λ p q i → antisym (p i) (q i)
      }

----------------------------------------------------------
-- Category of preorders

record isMonotone (A : Preorder 𝑖) (B : Preorder 𝑗) (f : SetoidHom ′ ⟨ A ⟩ ′ ′ ⟨ B ⟩ ′) : 𝒰 (𝑖 ､ 𝑗) where
  field monotone : ∀{a b : ⟨ A ⟩} -> (a ≤ b) -> ⟨ f ⟩ a ≤ ⟨ f ⟩ b

-- record isMonotone {A : 𝒰 _} {B : 𝒰 _} {{_ : Preorder 𝑖 on A}} {{_ : Preorder 𝑗 on B}} (f : (A -> B) :& isSetoidHom) : 𝒰 (𝑖 ､ 𝑗) where
--   field monotone : ∀{a b : A} -> (a ≤ b) -> ⟨ f ⟩ a ≤ ⟨ f ⟩ b
open isMonotone {{...}} public

-- record isMonotone {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isPreorder A}} {{_ : isPreorder B}} (f : A -> B) : 𝒰 (𝑖 ､ 𝑗) where
--   field monotone : ∀{a b : A} -> (a ≤ b) -> f a ≤ f b

Monotone : (A : Preorder 𝑖) (B : Preorder 𝑗) -> 𝒰 (𝑖 ､ 𝑗)
Monotone A B = _ :& isMonotone A B

module _ {A : Preorder 𝑖} {B : Preorder 𝑗} where
  _∼-Monotone_ : (f g : Monotone A B) -> 𝒰 _
  _∼-Monotone_ f g = ↳ f ∼ ↳ g
  -- record _∼-Monotone_ {A : Preorder 𝑖} {B : Preorder 𝑗} (f g : Monotone A B) : 𝒰 (𝑖 ､ 𝑗) where
  --   constructor incl
  --   field ⟨_⟩ : ↳ f ∼ ↳ g

  instance
    isEquivRel:∼-Monotone : isEquivRel _∼-Monotone_
    isEquivRel:∼-Monotone = isEquivRel:byDef refl (λ p -> sym p) (λ p q -> p ∙ q)
    -- (λ {f} -> incl (λ {a} -> refl)) (λ (incl p) -> incl (sym p)) {!!}

module _ {A : Preorder 𝑖} {B : Preorder 𝑗} where
  instance
    isSetoid:Monotone : isSetoid (Monotone A B)
    isSetoid:Monotone = isSetoid:byDef _∼-Monotone_
    -- (λ f g -> ⟨ f ⟩ ∼ ⟨ g ⟩) refl sym _∙_
    -- isSetoid._∼'_ isSetoid:Monotone f g = ⟨ f ⟩ ∼' ⟨ g ⟩
    -- isSetoid.isEquivRel:∼ isSetoid:Monotone = {!!}

-- unquoteDecl Monotone makeMonotone = #struct "Monotone" (quote isMonotone) "f" Monotone makeMonotone

{-
Category:Preorder : (𝑖 : 𝔏) -> Category _
⟨ Category:Preorder 𝑖 ⟩ = Preorder 𝑖
ICategory.Hom (of Category:Preorder 𝑖) = Monotone
ICategory._≣_ (of Category:Preorder 𝑖) f g = El f ≡ El g
ICategory.IEquiv:≣ (of Category:Preorder 𝑖) = {!!}
ICategory.id (of Category:Preorder 𝑖) = {!!}
ICategory._◆_ (of Category:Preorder 𝑖) = {!!}
ICategory.unit-l-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.unit-r-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.unit-2-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.assoc-l-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.assoc-r-◆ (of Category:Preorder 𝑖) = {!!}
ICategory._◈_ (of Category:Preorder 𝑖) = {!!}
-}







{-
  record _<_ (a b : A) : 𝒰 𝑖 where
    constructor _,_
    field π-≤ : a ≤ b
    field π-≁ : ¬ a ∼ b

  open _<_ public
-}
  -- a < b = a ≤ b ×-𝒰 (a ∼ b -> 𝟘-𝒰)



module _ {𝑗 : 𝔏 ^ 3} {A : 𝒰 _} {{_ : Preorder 𝑗 on A}} where
  by-∼-≤_ : {a b : A} -> (a ∼ b) -> a ≤ b
  by-∼-≤_ p = transp-≤ refl p reflexive

  命reflexive = by-∼-≤_

  infixl 10 by-∼-≤_

  _⟨_⟩-≤_ : (x : A) {y : A} {z : A} → x ≤ y → y ≤ z → x ≤ z
  _ ⟨ x≤y ⟩-≤ y≤z = x≤y ⟡ y≤z

  ⟨⟩-≤-syntax : (x : A) {y z : A} → x ≤ y → y ≤ z → x ≤ z
  ⟨⟩-≤-syntax = _⟨_⟩-≤_
  infixr 2 ⟨⟩-≤-syntax
  infix  3 _∎-≤
  infixr 2 _⟨_⟩-≤_

  _∎-≤ : (x : A) → x ≤ x
  _ ∎-≤ = reflexive

  _⟨_⟩-∼-≤_ : (x : A) {y : A} {z : A} → x ∼ y → y ≤ z → x ≤ z
  _ ⟨ x∼y ⟩-∼-≤ y≤z = transp-≤ (sym x∼y) refl y≤z -- x≤y ⟡ y≤z

  ⟨⟩-∼-≤-syntax : (x : A) {y z : A} → x ∼ y → y ≤ z → x ≤ z
  ⟨⟩-∼-≤-syntax = _⟨_⟩-∼-≤_
  infixr 2 ⟨⟩-∼-≤-syntax
  infixr 2 _⟨_⟩-∼-≤_

  _⟨_⟩-≤-∼_ : (x : A) {y : A} {z : A} → x ≤ y → y ∼ z → x ≤ z
  _ ⟨ x≤y ⟩-≤-∼ y∼z = transp-≤ refl y∼z x≤y -- x≤y ⟡ y≤z

  ⟨⟩-≤-∼-syntax : (x : A) {y z : A} → x ≤ y → y ∼ z → x ≤ z
  ⟨⟩-≤-∼-syntax = _⟨_⟩-≤-∼_
  infixr 2 ⟨⟩-≤-∼-syntax
  infixr 2 _⟨_⟩-≤-∼_

{-
{-

-}








{-
  _⟨_⟩-≤_ : (x : A) {y : A} {z : A} → x ≤ y → y ≤ z → x ≤ z
  _ ≤⟨ x≤y ⟩ y≤z = x≤y ⟡ y≤z

  ≤⟨⟩-syntax : (x : A) {y z : A} → x ≤ y → y ≤ z → x ≤ z
  ≤⟨⟩-syntax = _⟨_⟩-≤_
  infixr 2 ≤⟨⟩-syntax
  infix  3 _∎-≤
  infixr 2 _⟨_⟩-≤_

  _∎-≤ : (x : A) → x ≤ x
  _ ∎-≤ = reflexive

  _⟨_⟩-∼-≤_ : (x : A) {y : A} {z : A} → x ∼ y → y ≤ z → x ≤ z
  _ ∼⟨ x≤y ⟩≤ y≤z = {!!} -- x≤y ⟡ y≤z

  ⟨⟩-∼-≤-syntax : (x : A) {y z : A} → x ∼ y → y ≤ z → x ≤ z
  ⟨⟩-∼-≤-syntax = _⟨_⟩-∼-≤_
  infixr 2 ⟨⟩-∼-≤-syntax
  infixr 2 _⟨_⟩-∼-≤_

  _⟨_⟩-≤-∼_ : (x : A) {y : A} {z : A} → x ≤ y → y ∼ z → x ≤ z
  _ ≤⟨ x≤y ⟩∼ y≤z = {!!} -- x≤y ⟡ y≤z

  ⟨⟩-≤-∼-syntax : (x : A) {y z : A} → x ≤ y → y ∼ z → x ≤ z
  ⟨⟩-≤-∼-syntax = _⟨_⟩-≤-∼_
  infixr 2 ⟨⟩-≤-∼-syntax
  infixr 2 _⟨_⟩-≤-∼_
-}




  -- _∼⟨_⟩-≤_ : (x : A) {y : A} {z : A} → x ∼ y → y ≤ z → x ≤ z
  -- _ ∼≤⟨ x≤y ⟩ y≤z = {!!} -- x≤y ⟡ y≤z

  -- ∼≤⟨⟩-syntax : (x : A) {y z : A} → x ∼ y → y ≤ z → x ≤ z
  -- ∼≤⟨⟩-syntax = _∼⟨_⟩-≤_
  -- infixr 2 ∼≤⟨⟩-syntax
  -- -- infix  3 _∎-≤
  -- infixr 2 _∼⟨_⟩-≤_



{-
{-
unquoteDecl Preorder preorder = #struct "PreOrd" (quote isPreorder) "A" Preorder preorder

-}


-}
{-
module _ {A : 𝒰 𝑖} {{_ : isPreorder A}} where
  infix 30 _<_
  _<_ : A -> A -> 𝒰 𝑖
  a < b = (a ≤ b) ×-𝒰 (a ≡ b -> 𝟘-𝒰)

  instance
    Cast:≡→≤ : ∀{a b : A} -> Cast (a ≡ b) IAnything (a ≤ b)
    Cast.cast (Cast:≡→≤ {a = a} {b}) e = transport (λ i -> e (~ i) ≤ b) reflexive


-- record isPreorderHom {A B : Preorder} (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰₀ where

-- record PreorderHom (A B : Preorder) : 𝒰₀ where

instance
  -- ICategory:Preorder : ICategory Preorder (𝑖 , 𝑖 ,-)
  -- ICategory:Preorder = {!!}
{-
  ICategory.Hom ICategory:Preorder = PreorderHom
  ICategory.id ICategory:Preorder = {!!}
  ICategory._◆_ ICategory:Preorder = {!!}
-}

  isPreorder:ℕ : isPreorder ℕ
  isPreorder._≤_ isPreorder:ℕ = _≤-ℕ_
  isPreorder.reflexive isPreorder:ℕ = reflexive-ℕ
  isPreorder.trans-≤ isPreorder:ℕ = trans-≤-ℕ




--------------------------------------------------------------------
-- == Concatenation of preorders

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑖} {{_ : isPreorder A}} {{_ : isPreorder B}} where

  data _≤-⊕_ : (a b : A +-𝒰 B) -> 𝒰 𝑖 where
    left-≤ : ∀{a b : A} -> a ≤ b -> left a ≤-⊕ left b
    right-≤ : ∀{a b : B} -> a ≤ b -> right a ≤-⊕ right b
    left-right-≤ : ∀{a : A} {b : B} -> left a ≤-⊕ right b


  trans-≤-⊕ : ∀{a b c} -> (a ≤-⊕ b) -> (b ≤-⊕ c) -> a ≤-⊕ c
  trans-≤-⊕ (left-≤ p) (left-≤ q) = left-≤ (trans-≤ p q)
  trans-≤-⊕ (left-≤ x) left-right-≤ = left-right-≤
  trans-≤-⊕ (right-≤ p) (right-≤ q) = right-≤ (trans-≤ p q)
  trans-≤-⊕ left-right-≤ (right-≤ x) = left-right-≤

  reflexive-⊕ : ∀{a} -> (a ≤-⊕ a)
  reflexive-⊕ {left x} = left-≤ reflexive
  reflexive-⊕ {just x} = right-≤ reflexive


  instance
    isPreorder:+ : isPreorder (A +-𝒰 B)
    isPreorder._≤_ isPreorder:+ = _≤-⊕_
    isPreorder.reflexive isPreorder:+ {a = a} = reflexive-⊕ {a}
    isPreorder.trans-≤ isPreorder:+ {a = a} = trans-≤-⊕ {a = a}


_⊕-Preorder_ : Preorder 𝑖 -> Preorder 𝑖 -> Preorder 𝑖
A ⊕-Preorder B = preorder (⟨ A ⟩ +-𝒰 ⟨ B ⟩)

instance
  INotation:DirectSum:Preorder : INotation:DirectSum (Preorder 𝑖)
  INotation:DirectSum._⊕_ INotation:DirectSum:Preorder = _⊕-Preorder_


--------------------------------------------------------------------
-- == Example instances

instance
  isPreorder:⊤ : ∀{𝑖} -> isPreorder (Lift {j = 𝑖} 𝟙-𝒰)
  isPreorder._≤_ isPreorder:⊤ a b = `𝟙`
  isPreorder.reflexive isPreorder:⊤ = lift tt
  isPreorder.trans-≤ isPreorder:⊤ a b = lift tt

-}

-}
