module integers.props.mult.neutr where

open import naturals.def

open import pred-logic.def
open import pred-logic.props

open import integers.def
open import integers.ops

open import integers.props.add.neutr

open import integers.props.lemmas.incr-decr
open import integers.props.lemmas.incr-decr-idZ

-- Property: Left Neutrality with pos 1 for ℤ
leftNeutrℤ* : (x : ℤ) → (pos 1 * x) ≡ idℤ x
leftNeutrℤ* (pos x) = rightNeutr+ℤ+ (pos x)
leftNeutrℤ* (neg zero) = refl
leftNeutrℤ* (neg (suc zero)) = refl
leftNeutrℤ* (neg (suc (suc x))) = congruence decrementℤ (leftNeutrℤ* (neg (suc (x))))

-- Property: Right Neutrality with pos 1 for ℤ
rightNeutrℤ* : (x : ℤ) → (x * pos 1) ≡ idℤ x
rightNeutrℤ* (pos zero) = refl
rightNeutrℤ* (pos (suc x)) = congruence incrementℤ (rightNeutrℤ* (pos (x)))
rightNeutrℤ* (neg zero) = refl
rightNeutrℤ* (neg (suc zero)) = refl
rightNeutrℤ* (neg (suc (suc x))) = congruence decrementℤ (rightNeutrℤ* (neg (suc (x))))
