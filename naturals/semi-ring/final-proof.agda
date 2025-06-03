module naturals.semi-ring.final-proof where

open import pred-logic.def
open import type-variables.type-vars

open import naturals.ops
open import naturals.props.distr
open import naturals.semi-ring.prereqs

-- Proof: Show that ℕ under addition and multiplication form a semi-ring
record IsCommSemiRing
  (addIdentity : A) (multIdentity : A) (addOp : A → A → A) (multOp : A → A → A) : prop where
    field
      addCommMonoid : IsCommMonoid (addIdentity) (addOp)
      multCommMonoid : IsCommMonoid (multIdentity) (multOp)
      leftDistr : {x y z : A} → multOp (addOp x y) z ≡ addOp (multOp x z) (multOp y z)
      rightDistr : {x y z : A} → multOp x (addOp y z) ≡ addOp (multOp x y) (multOp x z)


-- Final Proof: ℕ forms a semi-ring under addition and multiplication with 0 as the additive identity and 1 as the multiplicative identity
semiRing+* : IsCommSemiRing (0) (1) (_+_) (_*_)
semiRing+* = record {
  addCommMonoid = addIsCommMonoid;
  multCommMonoid = multIsCommMonoid;
  leftDistr = λ {x} {y} {z} → leftDistrℕ {x} {y} {z};
  rightDistr = λ {x} {y} {z} → rightDistrℕ {x} {y} {z}}