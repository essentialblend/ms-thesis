module integers.props.mult.comm where

open import naturals.def

open import pred-logic.def
open import pred-logic.props

open import integers.def
open import integers.ops

open import integers.props.add.neutr
open import integers.props.add.comm
open import integers.props.add.assoc

open import integers.props.lemmas.incr-decr
open import integers.props.lemmas.incr-decr-idZ
open import integers.props.lemmas.idZ

-- Lemmas for comm of Multiplication
unfoldMult : (x : ℕ) (y : ℤ) → (y + (y * pos x)) ≡ (y * pos (suc x))
unfoldMult zero (pos zero) = refl
unfoldMult zero (pos (suc zero)) = refl
unfoldMult zero (pos (suc (suc y))) = propertyTransitivity (congruence incrementℤ (propertySymmetry (congruence (pos (suc y) +_) ((idx1-2 (pos y * pos zero)))))) (congruence incrementℤ (unfoldMult zero (pos (suc (y)))))
unfoldMult (suc x) (pos zero) = refl
unfoldMult (suc x) (pos (suc y)) = propertyTransitivity ((propertyTransitivity (commℤ+ (pos (suc y)) {pos (suc x) + (pos y * pos (suc x))}) (propertySymmetry (propertyTransitivity (incr[a+b]≡a+incr[b] (pos (suc x)) {pos y + (pos y * pos (suc x))}) (propertyTransitivity (congruence (pos (suc x) +_) (propertyTransitivity (incr[a+b]≡incr[a]+b (pos y) {pos y * pos (suc x)}) (propertySymmetry (commℤ+ (pos y * pos (suc x)) {pos (suc y)})))) (propertySymmetry (assocℤ+ (pos (suc x)) (pos y * pos (suc x)) {pos (suc y)}))))))) (congruence incrementℤ (congruence (pos (suc x) +_) (unfoldMult (suc x) (pos (y))))) 
unfoldMult zero (neg zero) = refl
unfoldMult zero (neg (suc zero)) = refl
unfoldMult zero (neg (suc (suc y))) = propertyTransitivity (congruence decrementℤ (congruence (neg (suc y) +_) (propertySymmetry (idx1-2 (neg y * pos 0))))) (congruence decrementℤ (unfoldMult zero (neg (suc (y)))))
unfoldMult (suc x) (neg zero) = refl
unfoldMult (suc x) (neg (suc y)) = propertyTransitivity (propertyTransitivity (commℤ+ (neg (suc y)) {neg (suc x) + (neg y * pos (suc x))}) (propertySymmetry (propertyTransitivity (decr[a+b]≡a+decr[b] (neg (suc x)) {neg y + (neg y * pos (suc x))}) (propertyTransitivity (propertySymmetry (propertyTransitivity (commℤ+ (neg (suc y)) {neg (suc x) + (neg y * pos (suc x))}) (propertyTransitivity (assocℤ+ (neg (suc x)) (neg y * pos (suc x)) {neg (suc y)}) (congruence (neg (suc x) +_) (propertySymmetry (propertyTransitivity (decr[a+b]≡decr[a]+b (neg y) {neg y * pos (suc x)}) (commℤ+ (neg (suc y)) {neg y * pos (suc x)}))))))) (commℤ+ (neg (suc y)) {neg (suc x) + (neg y * pos (suc x))}))))) (congruence decrementℤ (congruence (neg (suc x) +_) (unfoldMult (suc x) (neg (y)))))

unfoldMult2 : (x : ℕ) (y : ℤ) → (negateℤ y + (y * neg x)) ≡ (y * (neg (suc x)))
unfoldMult2 zero (pos zero) = refl
unfoldMult2 zero (pos (suc zero)) = propertyTransitivity (propertyTransitivity refl (propertySymmetry (decr[a+b]≡decr[a]+b (idℤ (neg zero)) {(pos zero * neg zero)}))) (congruence decrementℤ (unfoldMult2 zero (pos (zero))))
unfoldMult2 zero (pos (suc (suc y))) = propertyTransitivity (congruence decrementℤ (congruence (neg (suc y) +_) (propertySymmetry (idx1-2 (pos y * neg zero))))) (congruence decrementℤ (unfoldMult2 zero (pos (suc y))))
unfoldMult2 (zero) (neg zero) = refl
unfoldMult2 (zero) (neg (suc y)) = propertyTransitivity (propertySymmetry (propertyTransitivity (incr[a+b]≡incr[a]+b (pos y) {neg y * neg zero}) (congruence (pos (suc y) +_) (propertySymmetry (idℤa*b≡a*b (neg y) (neg zero)))))) (congruence incrementℤ (unfoldMult2 (zero) (neg (y))))
unfoldMult2 (suc x) (pos zero) = refl
unfoldMult2 (suc x) (pos (suc zero)) = congruence (neg (suc (suc x)) +_) (unfoldMult2 (suc x) (pos (zero)))
unfoldMult2 (suc x) (pos (suc (suc y))) = propertyTransitivity (propertyTransitivity (propertySymmetry (assocℤ+ (neg (suc (suc y))) (neg (suc x)))) (propertyTransitivity (congruence (λ l → (decrementℤ l) + (pos (suc y) * neg (suc x))) (commℤ+ (neg (suc y)) {neg (suc x)})) (assocℤ+ (neg (suc (suc x))) (neg (suc y))))) (congruence (neg (suc (suc x)) +_) (unfoldMult2 (suc x) (pos (suc y))))
unfoldMult2 (suc x) (neg zero) = refl
unfoldMult2 (suc x) (neg (suc zero)) = refl
unfoldMult2 (suc x) (neg (suc (suc y))) = propertyTransitivity (propertyTransitivity (propertySymmetry (assocℤ+ (pos (suc (suc y))) (pos (suc x)) {neg (suc y) * neg (suc x)})) (propertyTransitivity ( (congruence (λ l → (incrementℤ l) + (neg (suc y) * neg (suc x))) (commℤ+ (pos (suc y)) {pos (suc x)}))) (assocℤ+ (pos (suc (suc x))) (pos (suc y)) {neg (suc y) * neg (suc x)}))) (congruence (pos (suc (suc x)) +_) (unfoldMult2 (suc x) (neg (suc y))))

-- Property: ℤ multiplication is commutative
commℤ* : (x : ℤ) {y : ℤ} → (x * y) ≡ (y * x)
commℤ* (pos zero) {y} = propertySymmetry (rightZero+ℤ* y)
commℤ* (pos (suc x)) {y} =  propertyTransitivity (congruence (y +_) (commℤ* (pos (x)) {y})) (unfoldMult x y)
commℤ* (neg zero) {y} = propertySymmetry (rightZero-ℤ* y)
commℤ* (neg (suc x)) {y} = propertyTransitivity (congruence (negateℤ y +_) (commℤ* (neg (x)) {y})) (unfoldMult2 x y)
