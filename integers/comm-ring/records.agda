module integers.comm-ring.records where

open import pred-logic.def
open import type-variables.type-vars

-- Record-type: Monoid
record IsMonoidℤ
  (e : A) (idFunc : A → A) (_∙_ : A → A → A) : prop where
    field
      -- Left Neutrality
      leftNeutr  : {x : A} → (e ∙ x) ≡ idFunc x
      -- Right Neutrality
      rightNeutr : {x : A} → (x ∙ e) ≡ idFunc x
      -- Associativity
      assoc   : {x y z : A} → ((x ∙ y) ∙ z) ≡ (x ∙ (y ∙ z))

-- Record-type: Commutative Monoid
record IsCommMonoidℤ
  (e : A) (idFunc : A → A) (_∙_ : A → A → A) : prop where
    field
      -- Is Monoid
      isMonoidℤ  : IsMonoidℤ (e) (idFunc) (_∙_)
      -- Commutativity
      comm : {x y : A} → (x ∙ y) ≡ (y ∙ x)

-- Record-type: Group
record IsGroupℤ
  (e : A) (idFunc : A → A) (negFunc : A → A)  (_∙_ : A → A → A) : prop where
    field
      -- Is Monoid
      isMonoidℤ : IsMonoidℤ (e) (idFunc) (_∙_) 
      -- inv
      leftInv : {x : A} → ((negFunc x) ∙ x) ≡ e
      rightInv : {x : A} → (x ∙ (negFunc x)) ≡ e

-- Record-type: Abelian Group
record IsAbelianGroupℤ (e : A) (idFunc : A → A) (negFunc : A → A)  (_∙_ : A → A → A) : prop where
    field
      -- Is Group
      isGroupℤ : IsGroupℤ (e) (idFunc) (negFunc) (_∙_) 
      -- comm
      isComm : {x y : A} → (x ∙ y) ≡ (y ∙ x)

-- Record-type: Ring
record IsRingℤ
  (additiveId : A) (multId : A) (idFunc : A → A) (negFunc : A → A) (addOp : A → A → A) (multOp : A → A → A) : prop where
    field
      -- ℤ is an abelian group under addition.
      isAbelianGroup : IsAbelianGroupℤ (additiveId) (idFunc) (negFunc) (addOp)
      -- ℤ is a monoid with multiplication.
      isMonoidℤ : IsMonoidℤ (multId) (idFunc) (multOp)

-- Record-type: Commutative Ring
record IsCommRingℤ
  (additiveId : A) (multId : A) (idFunc : A → A) (negFunc : A → A) (addOp : A → A → A) (multOp : A → A → A) : prop where
    field
      -- ℤ is a ring
      isRingℤ : IsRingℤ (additiveId) (multId) (idFunc) (negFunc) (addOp) (multOp) 
      -- ℤ is commutative monoid
      isCommMonoidℤ : IsCommMonoidℤ (multId) (idFunc) (multOp)