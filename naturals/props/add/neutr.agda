module naturals.props.add.neutr where

open import naturals.def
open import naturals.ops

open import pred-logic.def
open import pred-logic.props

-- Left neutrality: 0 + n ≡ n 
leftNeutrℕ+ : {n : ℕ} → (0 + n) ≡ n
leftNeutrℕ+ {n} = refl

-- Right neutrality: n + 0 ≡ n
rightNeutrℕ+ : {n : ℕ} → (n + 0) ≡ n
rightNeutrℕ+ {zero}  = refl
rightNeutrℕ+ {suc n} = congruence suc (rightNeutrℕ+ {n})
