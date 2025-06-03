module naturals.props.mult.assoc where

open import naturals.def
open import naturals.ops

open import pred-logic.def
open import pred-logic.props

open import naturals.props.distr

-- Associativity under ℕ multiplication.
assocℕ* : {m n p : ℕ} → ((m * n) * p) ≡ (m * (n * p))
assocℕ* {zero} {n} {p} = refl
assocℕ* {suc m} {n} {p} = propertyTransitivity (leftDistrℕ {n} {m * n} {p}) (congruence ((n * p) +_) (assocℕ* {m} {n} {p}))
