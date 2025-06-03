module integers.comm-ring.final-proof where

open import naturals.def

open import integers.def
open import integers.ops

open import integers.comm-ring.prereqs
open import integers.comm-ring.records

-- FINAL PROOFS

-- Proof: ℤ is a ring
ℤIsRing : IsRingℤ (pos zero) (pos 1) (idℤ) (negateℤ) (_+_) (_*_)
ℤIsRing = record {
  isAbelianGroup = ℤIsCommGroup;
  isMonoidℤ = ℤMultIsMonoid}

-- Proof: ℤ is a commutative ring.
ℤIsCommRing : IsCommRingℤ (pos zero) (pos 1) (idℤ) (negateℤ) (_+_) (_*_)
ℤIsCommRing = record {
  isRingℤ = ℤIsRing;
  isCommMonoidℤ = ℤMultIsCommMonoid }

