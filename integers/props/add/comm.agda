module integers.props.add.comm where

open import naturals.def

open import pred-logic.def
open import pred-logic.props

open import integers.def
open import integers.ops

open import integers.props.add.neutr

open import integers.props.lemmas.incr-decr
open import integers.props.lemmas.incr-decr-idZ


-- Property: Integer addition is commutative.
commℤ+ : (x : ℤ) {y : ℤ} → (x + y) ≡ (y + x)
commℤ+ (pos zero) {y} = propertySymmetry (rightNeutr+ℤ+ y)
commℤ+ (pos (suc zero)) {y} = (propertyTransitivity (propertyTransitivity (propertySymmetry (incrℤidℤ≡incrℤ y)) (congruence incrementℤ (propertySymmetry (rightNeutr+ℤ+ y)))) (incr[a+b]≡a+incr[b] (y) {pos zero}))
commℤ+ (pos (suc (suc x))) {y} = propertyTransitivity (congruence incrementℤ (commℤ+ (pos (suc (x))) {y})) (incr[a+b]≡a+incr[b] y {pos (suc x)})
commℤ+ (neg zero) {y} = propertySymmetry (rightNeutr-ℤ+ y)
commℤ+ (neg (suc x)) {y} = propertyTransitivity (propertyTransitivity (propertySymmetry (decr[a+b]≡decr[a]+b (neg x) {y})) (congruence decrementℤ (commℤ+ (neg x) {y}))) (decr[a+b]≡a+decr[b] y {neg x})
