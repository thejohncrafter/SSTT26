open import Agda.Builtin.Equality

module HEq where

infix 4 _≅_

data _≅_ {A : Set} (x : A) : {B : Set} (y : B) → Set where
  refl : x ≅ x

≅-symm : {A B : Set} {x : A} {y : B} → x ≅ y → y ≅ x
≅-symm refl = refl

≡-of-≅ : {A : Set} {x y : A} → x ≅ y → x ≡ y
≡-of-≅ refl = refl

≅-of-≡ : {A : Set} {x y : A} → x ≡ y → x ≅ y
≅-of-≡ refl = refl

module ≅-Reasoning where
  infix  1 begin_
  infixr 2 step-≅-| step-≅-⟩
  infix  3 _∎

  {-begin_
    : {P : Set}
    → P → P
  begin x≅y = x≅y-}
  begin_
    : {A B : Set}
    → {x : A} {y : B}
    → x ≅ y → x ≅ y
  begin x≅y = x≅y

  step-≅-|
    : {A B : Set}
    → (x : A) {y : B} → x ≅ y → x ≅ y
  step-≅-| x x≅y = x≅y

  step-≅-⟩
    : {A B C : Set}
    → (x : A) {y : B} {z : C} → y ≅ z → x ≅ y → x ≅ z
  step-≅-⟩ x refl refl = refl

  syntax step-≅-| x x≅y      =  x ≅⟨⟩ x≅y
  syntax step-≅-⟩ x y≅z x≅y  =  x ≅⟨  x≅y  ⟩ y≅z

  _∎
    : {A : Set}
    → (a : A) → a ≅ a
  a ∎ = refl

open ≅-Reasoning public
