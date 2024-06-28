
module Agora.Category.Std.Closure.Exponential.Definition where

open import Agora.Conventions

open import Agora.Setoid.Morphism
open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
-- open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Category.Instance.2Category
open import Agora.Category.Std.Category.Instance.CategoryLike
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition

open import Agora.Category.Std.Limit.Specific.Product.Definition
open import Agora.Category.Std.Limit.Specific.Product.Instance.Functor
open import Agora.Category.Std.Category.Structured.FiniteProduct.Definition
open import Agora.Category.Std.Functor.Adjoint.Definition
open import Agora.Category.Std.Functor.Constant
open import Agora.Category.Std.Category.Construction.Product
open import Agora.Category.Std.Limit.Specific.Product.Instance.Functor

-- module _ {𝒞 : 𝒰 _} {{_ : FiniteProductCategory 𝑖 on 𝒞}} where
module _ {𝒞 : Category 𝑖} {{_ : hasFiniteProducts 𝒞}} where

  isExponential : (X : Obj 𝒞) -> 𝒰 𝑖
  isExponential X = Functor 𝒞 𝒞 :& isAdjoint (⧼ id-𝐂𝐚𝐭 , Const ⟨ X ⟩ ⧽-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 (⊓⃨ since isFunctor:⊓))

record hasExponentials (𝒞 : FiniteProductCategory 𝑖) : 𝒰 𝑖 where
  field Exponential : ∀(X : ⟨ 𝒞 ⟩) -> isExponential (obj X)

open hasExponentials {{...}} public

CartesianClosedCategory : ∀ 𝑖 -> 𝒰 _
CartesianClosedCategory 𝑖 = FiniteProductCategory 𝑖 :& hasExponentials

module _ {𝒞 : 𝒰 _} {{_ : CartesianClosedCategory 𝑖 on 𝒞}} where
  [_,_] : 𝒞 -> 𝒞 -> 𝒞
  [ X , Y ] = ⟨ Exponential X ⟩ Y

  curry : ∀{a b c : 𝒞} -> (a ⊓ b ⟶ c) -> a ⟶ [ b , c ]
  curry {b = b} = cofree {{of Exponential b}}

  uncurry : ∀{a b c : 𝒞} -> a ⟶ [ b , c ] -> (a ⊓ b ⟶ c)
  uncurry {b = b} = free {{of Exponential b}}

  [map_,_] : {a b : 𝒞} -> (f : a ⟶ b) -> (x : 𝒞) -> [ b , x ] ⟶ [ a , x ]
  [map f , Y ] = curry (map-⊓ (id , f) ◆ uncurry id)


