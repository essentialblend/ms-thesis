module integers.comm-ring.prereqs where

open import type-variables.type-vars

open import pred-logic.def

open import naturals.def

open import integers.def
open import integers.ops

open import integers.props.add.neutr
open import integers.props.add.comm
open import integers.props.add.assoc
open import integers.props.add.inv

open import integers.props.mult.neutr
open import integers.props.mult.comm
open import integers.props.mult.assoc

open import integers.comm-ring.records

-- i- Addition Monoid Proofs 
-- Proof: Addition with pos 0 is a monoid.
ℤAddIsMonoid : IsMonoidℤ (pos zero) (idℤ) (_+_)
ℤAddIsMonoid = record {
  -- Proof for left neutrality.
  leftNeutr = λ {x} → leftNeutr+ℤ+ x;
  -- Proof for right neutrality.
  rightNeutr = λ {x} → rightNeutr+ℤ+ x;
  -- Proof for assoc
  assoc = λ {x} {y} {z} → assocℤ+ x y {z} }

-- Addition with pos 0 is a commutative monoid.
ℤAddIsCommMonoid : IsCommMonoidℤ (pos zero) (idℤ) (_+_)
ℤAddIsCommMonoid = record {
  -- Proof for monoid.
  isMonoidℤ = ℤAddIsMonoid;
  -- Proof for commutativity.
  comm = λ {x} {y} → commℤ+ x {y}}

-- ii- Multiplication  Monoid Proofs 

-- Multiplication with pos 1 is a monoid.
ℤMultIsMonoid : IsMonoidℤ (pos 1) (idℤ) (_*_)
ℤMultIsMonoid = record {
  -- Proof for left neutrality.
  leftNeutr = λ {x} → leftNeutrℤ* x;
  -- Proof for right neutrality.
  rightNeutr = λ {x} → rightNeutrℤ* x;
  -- Proof for assoc.
  assoc = λ {x} {y} {z} → assocℤ* x y {z} }

-- Multiplication with pos 1 is a commutative monoid.
ℤMultIsCommMonoid : IsCommMonoidℤ (pos 1) (idℤ) (_*_)
ℤMultIsCommMonoid = record {
  -- Proof for monoid
  isMonoidℤ = ℤMultIsMonoid;
  -- Proof for commutativity.
  comm = λ {x} {y} → commℤ* x {y}}

-- Proof: ℤ is a group
ℤIsGroup : IsGroupℤ (pos zero) (idℤ) (negateℤ) (_+_)
ℤIsGroup = record {
  isMonoidℤ = ℤAddIsMonoid;
  leftInv = λ {x} → leftAddInvℤ+ x;
  rightInv = λ {x} → rightAddInvℤ+ x }

-- Proof: ℤ is a commutative group
ℤIsCommGroup : IsAbelianGroupℤ (pos zero) (idℤ) (negateℤ) (_+_)
ℤIsCommGroup = record {
  isGroupℤ = ℤIsGroup;
  isComm = λ {x} {y} → commℤ+ x {y} }
