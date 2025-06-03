module integers.props.lemmas.incr-decr where

open import type-variables.bool

open import naturals.def
open import naturals.ops renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import pred-logic.def
open import pred-logic.props

open import integers.def
open import integers.ops
open import integers.props.lemmas.incr-decr-idZ
open import integers.props.lemmas.idZ


-- a)
incr[a+b]≡incr[a]+b : (a : ℤ) {b : ℤ} → (incrementℤ (a + b)) ≡ ((incrementℤ a) + b)
incr[a+b]≡incr[a]+b (pos zero) {b} = incrℤidℤ≡incrℤ b
incr[a+b]≡incr[a]+b (pos (suc a)) = refl
incr[a+b]≡incr[a]+b (neg zero) {b} = incrℤidℤ≡incrℤ b
incr[a+b]≡incr[a]+b (neg (suc zero)) {b} = incrDecrℤ≡ b
incr[a+b]≡incr[a]+b (neg (suc (suc zero))) {b} = propertyTransitivity (incrDecrℤ≡ (decrementℤ b)) (idℤDecr≡Decr b)
incr[a+b]≡incr[a]+b (neg (suc (suc (suc a)))) {b} = propertyTransitivity (propertySymmetry (decrIncr≡IncrDecr (decrementℤ (Itℕ (decrementℤ b) decrementℤ a)))) (congruence decrementℤ (incr[a+b]≡incr[a]+b (neg (suc (suc (a)))) {b}))

-- b)
incr[a+b]≡a+incr[b] : (a : ℤ) {b : ℤ} → (incrementℤ (a + b)) ≡ (a + (incrementℤ b))
incr[a+b]≡a+incr[b] (pos zero) {b} = propertySymmetry (idℤ-Incr≡Incr-idℤ b)
incr[a+b]≡a+incr[b] (pos (suc zero)) {pos zero} = refl
incr[a+b]≡a+incr[b] (pos (suc (suc a))) {pos zero} = congruence incrementℤ (incr[a+b]≡a+incr[b] (pos (suc a)) {pos zero})
incr[a+b]≡a+incr[b] (pos (suc zero)) {pos (suc b)} = refl
incr[a+b]≡a+incr[b] (pos (suc (suc a))) {pos (suc b)} = congruence incrementℤ (incr[a+b]≡a+incr[b] (pos (suc a)) {pos (suc b)})
incr[a+b]≡a+incr[b] (pos (suc zero)) {neg zero} = refl
incr[a+b]≡a+incr[b] (pos (suc (suc a))) {neg zero} = congruence incrementℤ (incr[a+b]≡a+incr[b] (pos (suc a)) {neg zero})
incr[a+b]≡a+incr[b] (pos (suc zero)) {neg (suc b)} = refl
incr[a+b]≡a+incr[b] (pos (suc (suc a))) {neg (suc b)} = congruence incrementℤ (incr[a+b]≡a+incr[b] (pos (suc a)))
incr[a+b]≡a+incr[b] (neg zero) {b} = propertySymmetry (idℤ-Incr≡Incr-idℤ (b))
incr[a+b]≡a+incr[b] (neg (suc zero)) {pos b} = incrDecrℤ≡ (pos b)
incr[a+b]≡a+incr[b] (neg (suc zero)) {neg zero} = refl
incr[a+b]≡a+incr[b] (neg (suc zero)) {neg (suc zero)} = refl
incr[a+b]≡a+incr[b] (neg (suc zero)) {neg (suc (suc b))} = refl
incr[a+b]≡a+incr[b] (neg (suc (suc zero))) {pos zero} = refl
incr[a+b]≡a+incr[b] (neg (suc (suc zero))) {pos (suc b)} =  incrDecrℤ≡ (pos b)
incr[a+b]≡a+incr[b] (neg (suc (suc zero))) {neg zero} = refl
incr[a+b]≡a+incr[b] (neg (suc (suc zero))) {neg (suc zero)} = refl
incr[a+b]≡a+incr[b] (neg (suc (suc zero))) {neg (suc (suc b))} = refl
incr[a+b]≡a+incr[b] (neg (suc (suc (suc a)))) {b} = propertyTransitivity (propertyTransitivity (incrDecrℤ≡ (decrementℤ (Itℕ (decrementℤ b) decrementℤ a))) (propertyTransitivity refl (propertySymmetry (decrIncrℤ≡ (decrementℤ (Itℕ (decrementℤ b) decrementℤ a)))))) (congruence decrementℤ (incr[a+b]≡a+incr[b] (neg (suc (suc a))) {b}))

-- Decrement Lemmas
-- c)
decr[a+b]≡a+decr[b] : (a : ℤ) {b : ℤ} → (decrementℤ (a + b)) ≡ (a + (decrementℤ b))
decr[a+b]≡a+decr[b] (pos zero) {b} = propertySymmetry (idℤ-Decr≡Decr-idℤ b)
decr[a+b]≡a+decr[b] (pos (suc zero)) {pos zero} = refl
decr[a+b]≡a+decr[b] (pos (suc (suc a))) {pos zero} = propertyTransitivity (propertyTransitivity (decrIncrℤ≡ (Itℕ (pos 1) incrementℤ a)) (propertySymmetry (incrDecrℤ≡ (Itℕ (pos 1) incrementℤ a)))) (congruence incrementℤ (decr[a+b]≡a+decr[b] (pos (suc a)) {pos zero})) 
decr[a+b]≡a+decr[b] (pos (suc zero)) {pos (suc b)} = refl
decr[a+b]≡a+decr[b] (pos (suc (suc a))) {pos (suc zero)} = propertyTransitivity (propertyTransitivity (decrIncrℤ≡ (Itℕ (pos 2) incrementℤ a)) (propertySymmetry (incrDecrℤ≡ (Itℕ (pos 2) incrementℤ a)))) (congruence incrementℤ (decr[a+b]≡a+decr[b] (pos (suc a)) {pos (suc zero)}))
decr[a+b]≡a+decr[b] (pos (suc (suc a))) {pos (suc (suc b))} = propertyTransitivity (propertyTransitivity (decrIncrℤ≡ (Itℕ (pos (suc (suc (suc b)))) incrementℤ a)) (propertySymmetry (incrDecrℤ≡ (Itℕ (pos (suc (suc (suc b)))) incrementℤ a)))) (congruence incrementℤ (decr[a+b]≡a+decr[b] (pos (suc a)) {pos (suc (suc b))}))
decr[a+b]≡a+decr[b] (pos (suc zero)) {neg zero} = refl
decr[a+b]≡a+decr[b] (pos (suc (suc a))) {neg zero} = propertyTransitivity (decrIncr≡IncrDecr (Itℕ (⟨ true ⟩ 1) incrementℤ a)) (congruence incrementℤ (decr[a+b]≡a+decr[b] (pos (suc a)) {neg zero}))
decr[a+b]≡a+decr[b] (pos (suc zero)) {neg (suc b)} = decrIncrℤ≡ (neg (suc b))
decr[a+b]≡a+decr[b] (pos (suc (suc a))) {neg (suc zero)} = propertyTransitivity (decrIncr≡IncrDecr (Itℕ (⟨ true ⟩ zero) incrementℤ a)) (congruence incrementℤ (decr[a+b]≡a+decr[b] (pos (suc a)) {neg (suc zero)}))
decr[a+b]≡a+decr[b] (pos (suc (suc a))) {neg (suc (suc b))} = propertyTransitivity (decrIncr≡IncrDecr (Itℕ (neg (suc b)) incrementℤ a)) (congruence incrementℤ (decr[a+b]≡a+decr[b] (pos (suc a)) {neg (suc (suc b))}))
decr[a+b]≡a+decr[b] (neg zero) {pos zero} = refl
decr[a+b]≡a+decr[b] (neg zero) {pos (suc b)} = refl
decr[a+b]≡a+decr[b] (neg (suc zero)) {pos zero} = refl
decr[a+b]≡a+decr[b] (neg (suc (suc a))) {pos zero} = (congruence decrementℤ (decr[a+b]≡a+decr[b] (neg (suc a)) {pos zero}))
decr[a+b]≡a+decr[b] (neg (suc zero)) {pos (suc b)} = refl
decr[a+b]≡a+decr[b] (neg (suc (suc zero))) {pos (suc zero)} = refl
decr[a+b]≡a+decr[b] (neg (suc (suc (suc a)))) {pos (suc zero)} = congruence decrementℤ (decr[a+b]≡a+decr[b] (neg (suc (suc a))) {pos (suc zero)})
decr[a+b]≡a+decr[b] (neg (suc (suc a))) {pos (suc (suc b))} = congruence decrementℤ (decr[a+b]≡a+decr[b] (neg (suc a)) {pos (suc (suc b))})
decr[a+b]≡a+decr[b] (neg zero) {neg zero} = refl
decr[a+b]≡a+decr[b] (neg zero) {neg (suc b)} = refl
decr[a+b]≡a+decr[b] (neg (suc zero)) {neg zero} = refl
decr[a+b]≡a+decr[b] (neg (suc (suc a))) {neg zero} = congruence decrementℤ (decr[a+b]≡a+decr[b] (neg (suc a)) {neg zero})
decr[a+b]≡a+decr[b] (neg (suc zero)) {neg (suc b)} = refl
decr[a+b]≡a+decr[b] (neg (suc (suc a))) {neg (suc zero)} = congruence decrementℤ (decr[a+b]≡a+decr[b] (neg (suc a)) {neg (suc zero)})
decr[a+b]≡a+decr[b] (neg (suc (suc a))) {neg (suc (suc b))} = congruence decrementℤ (decr[a+b]≡a+decr[b] (neg (suc a)) {neg (suc (suc b))})

-- d)
decr[a+b]≡decr[a]+b : (a : ℤ) {b : ℤ} → decrementℤ (a + b) ≡ ((decrementℤ a) + b)
decr[a+b]≡decr[a]+b (pos zero) {b} = Decridℤ≡Decr b
decr[a+b]≡decr[a]+b (pos (suc zero)) {b} = decrIncrℤ≡ b
decr[a+b]≡decr[a]+b (pos (suc (suc a))) {b} = propertyTransitivity (decrIncrℤ≡ (pos (suc a) + b)) (idℤ+≡+ (pos (suc a)) {b})
decr[a+b]≡decr[a]+b (neg zero) {b} = Decridℤ≡Decr b
decr[a+b]≡decr[a]+b (neg (suc a)) = refl

-- e)
incr[decr[posa]*z]≡a*z : (a : ℕ) {z : ℤ} → (pos a * z) ≡ (incrementℤ (decrementℤ (pos a)) * z)
incr[decr[posa]*z]≡a*z zero = refl
incr[decr[posa]*z]≡a*z (suc a) = refl
