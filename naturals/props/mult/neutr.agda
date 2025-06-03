module naturals.props.mult.neutr where

open import naturals.def
open import naturals.ops

open import naturals.props.add.neutr

open import pred-logic.def
open import pred-logic.props

-- Left Neutrality: 
leftNeutrℕ* : {n : ℕ} → (1 * n) ≡ n
leftNeutrℕ* {n} = rightNeutrℕ+ {n}

-- Right Neutrality:
rightNeutrℕ* : {n : ℕ} → (n * 1) ≡ n
rightNeutrℕ* {zero} = refl
rightNeutrℕ* {suc n} = congruence suc (rightNeutrℕ* {n})
