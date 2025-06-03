module naturals.semi-ring.records where

open import pred-logic.def
open import type-variables.type-vars

-- Record: Monoid
record IsMonoid
  (e : A) (_∙_ : A → A → A) : prop where
    field
      leftNeutr  : {x : A} → (e ∙ x) ≡ x
      rightNeutr : {x : A} → (x ∙ e) ≡ x
      assoc   : {x y z : A} → ((x ∙ y) ∙ z) ≡ (x ∙ (y ∙ z))

-- Record: Commutative Monoid
record IsCommMonoid
  (e : A) (_∙_ : A → A → A) : prop where
    field
      isMonoid : IsMonoid e (_∙_)
      isComm : { x y : A } → (x ∙ y) ≡ (y ∙ x)