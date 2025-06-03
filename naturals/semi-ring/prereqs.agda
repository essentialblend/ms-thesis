module naturals.semi-ring.prereqs where

open import type-variables.type-vars

open import pred-logic.def
open import pred-logic.props

open import naturals.def
open import naturals.ops

open import naturals.props.add.neutr
open import naturals.props.add.assoc
open import naturals.props.add.comm

open import naturals.props.mult.neutr
open import naturals.props.mult.assoc
open import naturals.props.mult.comm

open import naturals.props.distr


-- Definition: Monoid
record IsMonoid
  (e : A) (_∙_ : A → A → A) : prop where
    field
      leftNeutr  : {x : A} → (e ∙ x) ≡ x
      rightNeutr : {x : A} → (x ∙ e) ≡ x
      assoc   : {x y z : A} → ((x ∙ y) ∙ z) ≡ (x ∙ (y ∙ z))

-- Definition: Commutative Monoid
record IsCommMonoid
  (e : A) (_∙_ : A → A → A) : prop where
    field
      isMonoid : IsMonoid e (_∙_)
      isComm : { x y : A } → (x ∙ y) ≡ (y ∙ x)



-- Proof: Show that ℕ under + is a (commutative) monoid
addIsMonoid : IsMonoid (zero) (_+_)
addIsMonoid = record {
  leftNeutr  = leftNeutrℕ+;
  rightNeutr = rightNeutrℕ+;
  assoc   = λ {x} {y} {z} → assocℕ+ {x} {y} {z} }

addIsCommMonoid : IsCommMonoid (zero) (_+_)
addIsCommMonoid = record {
  isMonoid = addIsMonoid;
  isComm = λ {x} {y} → commℕ+ x {y} }

-- Proof: Show that ℕ under * is a (commutative) monoid
multIsMonoid : IsMonoid (1) (_*_)
multIsMonoid = record {
  leftNeutr = leftNeutrℕ*;
  rightNeutr = rightNeutrℕ*;
  assoc = λ {x} {y} {z} →  assocℕ* {x} {y} {z} }

multIsCommMonoid : IsCommMonoid (1) (_*_)
multIsCommMonoid = record {
  isMonoid = multIsMonoid;
  isComm = λ {x} {y} → commℕ* x {y} }




