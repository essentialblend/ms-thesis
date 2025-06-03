module naturals.props.add.assoc where

open import naturals.def
open import naturals.ops

open import pred-logic.def
open import pred-logic.props

{- Property: Associativity over ℕ Addition -}
assocℕ+ : {l m n : ℕ} → ((l + m) + n) ≡ (l + (m + n))
assocℕ+ {zero} {m} {n} = refl
assocℕ+ {suc l} {m} {n} = congruence suc (assocℕ+ {l} {m} {n})
