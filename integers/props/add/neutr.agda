module integers.props.add.neutr where

open import naturals.def

open import pred-logic.def
open import pred-logic.props

open import integers.def
open import integers.ops
open import integers.props.lemmas.incr-decr
open import integers.props.lemmas.incr-decr-idZ
open import integers.props.lemmas.idZ


-- Property: Left Neutrality for ℤ
leftNeutr+ℤ+ : ∀ (x : ℤ) → ((pos zero) + x) ≡ idℤ x
leftNeutr+ℤ+ (pos x) = refl
leftNeutr+ℤ+ (neg x) = refl

-- Optional: Left Neutrality for neg zero.
leftNeutr-ℤ+ : (x : ℤ) → ((neg zero) + x) ≡ idℤ x
leftNeutr-ℤ+ (pos zero) = refl
leftNeutr-ℤ+ (pos (suc y)) = refl
leftNeutr-ℤ+ (neg zero) = refl
leftNeutr-ℤ+ (neg (suc y)) = refl


-- Property: Right Neutrality for ℤ
rightNeutr+ℤ+ : (x : ℤ) → (x + pos zero) ≡ idℤ x
rightNeutr+ℤ+ (pos zero) = refl
rightNeutr+ℤ+ (pos (suc x)) = propertyTransitivity (propertySymmetry (incr[a+b]≡incr[a]+b (pos (x)) {pos zero})) (congruence incrementℤ (rightNeutr+ℤ+ (pos (x))))
rightNeutr+ℤ+ (neg zero) = refl
rightNeutr+ℤ+ (neg (suc zero)) = refl
rightNeutr+ℤ+ (neg (suc (suc x))) =  congruence decrementℤ (rightNeutr+ℤ+ (neg (suc (x))))

-- Optional: Right Neutrality for neg zero
rightNeutr-ℤ+ : (x : ℤ) → (x + (neg zero)) ≡ idℤ x
rightNeutr-ℤ+ (pos zero) = refl
rightNeutr-ℤ+ (pos (suc x)) = propertyTransitivity (propertySymmetry (incr[a+b]≡incr[a]+b (pos x) {neg zero})) (congruence incrementℤ (rightNeutr-ℤ+ (pos (x))))
rightNeutr-ℤ+ (neg zero) = refl
rightNeutr-ℤ+ (neg (suc zero)) = refl
rightNeutr-ℤ+ (neg (suc (suc x))) = congruence decrementℤ (rightNeutr-ℤ+ (neg (suc (x))))


-- Lemmas for zero multiplied by another number
-- Left: zero * n ≡ zero 
leftZero+ℤ* : (y : ℤ) → (pos zero * y) ≡ pos zero
leftZero+ℤ* y = refl

-- Right: n * zero ≡ zero
rightZero+ℤ* : (y : ℤ) → (y * pos zero) ≡ pos zero
rightZero+ℤ* (pos zero) = refl
rightZero+ℤ* (pos (suc zero)) = refl
rightZero+ℤ* (pos (suc (suc y))) = propertyTransitivity (propertySymmetry (idx1-2 (pos y * pos zero))) (rightZero+ℤ* (pos (suc y)))
rightZero+ℤ* (neg zero) = refl
rightZero+ℤ* (neg (suc zero)) = refl
rightZero+ℤ* (neg (suc (suc y))) = propertyTransitivity (propertySymmetry (idx1-2 (neg y * pos zero))) (rightZero+ℤ* (neg (suc y)))

-- Right: n * neg zero ≡ zero
rightZero-ℤ* : (y : ℤ) → (y * neg zero) ≡ pos zero
rightZero-ℤ* (pos zero) = refl
rightZero-ℤ* (pos (suc y)) = propertyTransitivity (idℤa*b≡a*b (pos y) (neg zero)) (rightZero-ℤ* (pos (y)))
rightZero-ℤ* (neg zero) = refl
rightZero-ℤ* (neg (suc y)) = propertyTransitivity (idℤa*b≡a*b (neg y) (neg zero)) (rightZero-ℤ* (neg (y)))
