module integers.props.add.inv where

open import naturals.def

open import pred-logic.def
open import pred-logic.props

open import integers.def
open import integers.ops
open import integers.props.lemmas.incr-decr
open import integers.props.lemmas.incr-decr-idZ

-- Lemma for Left Additive Inverse
addℤ→incrℤ : (x : ℕ) {y : ℕ} → (pos x + neg x) ≡ (pos (suc x) + neg (suc x))
addℤ→incrℤ zero = refl
addℤ→incrℤ (suc x) {zero} = propertySymmetry (incr[a+b]≡a+incr[b] (pos (suc x)) {neg (suc (suc x))})
addℤ→incrℤ (suc x) {suc y} = propertySymmetry (incr[a+b]≡a+incr[b] (pos (suc x)) {neg (suc (suc x))})

-- Property: Left Additive Inverse
leftAddInvℤ+ : (x : ℤ) → ((negateℤ x) + x) ≡ pos zero
leftAddInvℤ+ (pos zero) = refl
leftAddInvℤ+ (pos (suc zero)) = refl
leftAddInvℤ+ (pos (suc (suc x))) = propertyTransitivity (decr[a+b]≡a+decr[b] (neg (suc x)) {pos (suc (suc x))}) (leftAddInvℤ+ (pos (suc x)))
leftAddInvℤ+ (neg zero) = refl
leftAddInvℤ+ (neg (suc x)) = propertyTransitivity (propertySymmetry (addℤ→incrℤ (x) {zero})) (leftAddInvℤ+ (neg x))

-- Property: Right Additive Inverse
rightAddInvℤ+ : (x : ℤ) → (x + (negateℤ x)) ≡ pos zero
rightAddInvℤ+ (pos zero) = refl
rightAddInvℤ+ (pos (suc zero)) = refl
rightAddInvℤ+ (pos (suc (suc x))) = propertyTransitivity (incr[a+b]≡a+incr[b] (pos (suc x)) {neg (suc (suc x))}) (rightAddInvℤ+ (pos (suc (x))))
rightAddInvℤ+ (neg zero) = refl
rightAddInvℤ+ (neg (suc zero)) = refl
rightAddInvℤ+ (neg (suc (suc x))) = propertyTransitivity (decr[a+b]≡a+decr[b] (neg (suc x)) {pos (suc (suc x))}) (rightAddInvℤ+ (neg (suc (x))))
