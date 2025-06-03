module naturals.props.mult.comm where

open import naturals.def
open import naturals.ops

open import pred-logic.def
open import pred-logic.props

open import naturals.props.add.neutr
open import naturals.props.add.comm
open import naturals.props.add.assoc

open import naturals.props.mult.absorption

-- Lemma for commutativity of multiplication
distrRightSucℕ* : (y : ℕ) {x : ℕ} → (y * (suc x)) ≡ (y + (y * x))
distrRightSucℕ* zero {x} = refl
distrRightSucℕ* (suc y) {x} = propertyTransitivity (congruence suc (congruence (x +_) (distrRightSucℕ* (y) {x}))) (congruence suc (propertyTransitivity (propertySymmetry (assocℕ+ {x} {y} {y * x})) (propertyTransitivity (congruence (_+ (y * x)) (commℕ+ x {y})) (assocℕ+ {y} {x} {y * x}) )))


-- Main Proof: Commutativity of ℕ multiplication
commℕ* : (m : ℕ) {n : ℕ} → (m * n) ≡ (n * m)
commℕ* zero {n} = propertySymmetry (rightAbsorptionℕ* {n})
commℕ* (suc x) {y} = propertyTransitivity (congruence (y +_) (commℕ* x {y})) (propertySymmetry (distrRightSucℕ* y {x}))
