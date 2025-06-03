module naturals.semi-ring.prereqs where

open import naturals.def
open import naturals.ops

open import naturals.props.add.neutr
open import naturals.props.add.assoc
open import naturals.props.add.comm

open import naturals.props.mult.neutr
open import naturals.props.mult.assoc
open import naturals.props.mult.comm

open import naturals.semi-ring.records

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




