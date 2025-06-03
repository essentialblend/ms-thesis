module naturals.semi-ring.semi-ring where

open import naturals.semi-ring.prereqs

-- Proof: Show that ℕ under addition and multiplication form a semi-ring
{- record IsCommSemiRing
  (addIdentity : A) (multIdentity : A) (addOp : A → A → A) (multOp : A → A → A) : prop where
    field
      addCommMonoid : IsCommMonoid (addIdentity) (addOp)
      multCommMonoid : IsCommMonoid (multIdentity) (multOp)
      leftDistr : {x y z : A} → multOp (addOp x y) z ≡ addOp (multOp x z) (multOp y z)
      rightDistr : {x y z : A} → multOp x (addOp y z) ≡ addOp (multOp x y) (multOp x z) -}


-- FINAL PROOF
{- semiRing+* : IsCommSemiRing (0) (1) (_+_) (_*_)
semiRing+* = record {
  addCommMonoid = addIsCommMonoid;
  multCommMonoid = multIsCommMonoid;
  leftDistr = λ {x} {y} {z} → leftDistrℕ {x} {y} {z};
  rightDistr = λ {x} {y} {z} → rightDistrℕ {x} {y} {z}} -}