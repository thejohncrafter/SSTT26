
module OpsNotation where

record OpNotation
  (I : Set)
  (Op : I → Set)
  (F : (i : I) → Op i → Set)
  : Set where
  constructor mk-op-notation
  field
    _[_] : (i : I) → (σ : Op i) → F i σ
  infixl 25 _[_]

open OpNotation ⦃ ... ⦄ public
