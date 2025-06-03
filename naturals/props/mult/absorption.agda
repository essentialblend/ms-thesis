module naturals.props.mult.absorption where

open import naturals.def
open import naturals.ops

open import pred-logic.def
open import pred-logic.props

-- Left Absorption : 0 * n ≡ 0
leftAbsorptionℕ* : {n : ℕ} → (0 * n) ≡ 0
leftAbsorptionℕ* {zero} = refl
leftAbsorptionℕ* {suc n} = refl

-- Right Absorption : n * 0 ≡ 0
rightAbsorptionℕ* : {n : ℕ} → (n * 0) ≡ 0
rightAbsorptionℕ* {zero} = refl
rightAbsorptionℕ* {suc n} = rightAbsorptionℕ* {n}
