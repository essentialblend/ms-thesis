module naturals.props.distr where

open import naturals.def
open import naturals.ops

open import pred-logic.def
open import pred-logic.props

open import naturals.props.add.assoc
open import naturals.props.add.comm

-- Left Distributivity Law 
leftDistrℕ : {l m n : ℕ} → ((l + m) * n) ≡ ((l * n) + (m * n))
leftDistrℕ {zero} {m} {n} = refl
leftDistrℕ {suc l} {m} {n} = propertyTransitivity (congruence (λ x → n + x) (leftDistrℕ {l})) (propertySymmetry (assocℕ+ {n} {l * n} {m * n}))

-- Right Distributivity Law
rightDistrℕ : {l m n : ℕ} → (l * (m + n)) ≡ ((l * m) + (l * n))
rightDistrℕ {zero} {m} {n} = refl
rightDistrℕ {suc l} {m} {n} = propertyTransitivity (congruence (λ x → ((m + n) + x)) (rightDistrℕ {l} {m} {n})) (propertySymmetry  (propertyTransitivity (assocℕ+ {m} {(l * m)} {(n + (l * n))}) (propertySymmetry (propertyTransitivity (assocℕ+ {m} {n} {(l * m) + (l * n)}) (congruence (m +_) (propertyTransitivity (commℕ+ n {(l * m) + (l * n)}) (propertyTransitivity (assocℕ+ {l * m} {l * n} {n}) (congruence ((l * m) +_) (commℕ+ (l * n) {n})))))))))
