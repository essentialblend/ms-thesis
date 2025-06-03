module naturals.props.add.comm where

open import naturals.def
open import naturals.ops

open import pred-logic.def
open import pred-logic.props

open import naturals.props.add.neutr

-- Lemma
suc+ : (m n : ℕ) → (suc (n + m)) ≡ (n + (suc m))
suc+ m zero = refl
suc+ m (suc n) = congruence suc (suc+ m n)

-- Main Proof: Commutativity 
commℕ+ : (m : ℕ) {n : ℕ} → (m + n) ≡ (n + m)
commℕ+ zero {n} = propertySymmetry (rightNeutrℕ+ {n})
commℕ+ (suc m) {n} = propertyTransitivity (congruence suc (commℕ+ m {n})) (suc+ m n)
