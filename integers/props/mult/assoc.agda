module integers.props.mult.assoc where

open import naturals.def
open import naturals.ops renaming (_+_ to _ℕ+_; _*_ to _*ℕ_)


open import pred-logic.def
open import pred-logic.props

open import integers.def
open import integers.ops

open import integers.props.add.neutr

open import integers.props.lemmas.incr-decr
open import integers.props.lemmas.incr-decr-idZ
open import integers.props.lemmas.idZ
open import integers.props.lemmas.negZ

open import integers.props.distr

-- Property: ℤ multiplication is associative
assocℤ* : (x y : ℤ) {z : ℤ} → ((x * y) * z) ≡ (x * (y * z))
assocℤ* (pos zero) y = refl
assocℤ* (pos (suc x)) y {z} = propertyTransitivity (rightDistrℤ (y) (pos x * y) {z}) (congruence ((y * z) +_ ) (assocℤ* (pos (x)) y {z}))
assocℤ* (neg zero) y = refl
assocℤ* (neg (suc x)) y {z} = propertyTransitivity (propertyTransitivity (rightDistrℤ (negateℤ y) (neg x * y) {z}) (congruence (_+ ((neg x * y) * z)) (propertySymmetry (negℤ[a*b]≡[negℤa]*b y {z})))) (congruence (negateℤ (y * z) +_) (assocℤ* (neg (x)) y {z}))
