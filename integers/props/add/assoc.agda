module integers.props.add.assoc where

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


-- Property: ℤ addition is associative
assocℤ+ : (x y : ℤ) {z : ℤ} → ((x + y) + z) ≡ (x + (y + z))
assocℤ+ (pos zero) y {z} = (propertySymmetry (idℤ[a+b]≡idℤa+b (y) (z)))
assocℤ+ (pos (suc zero)) y {z} = propertySymmetry (incr[a+b]≡incr[a]+b y {z})
assocℤ+ (pos (suc (suc x))) y {z} = propertyTransitivity (propertySymmetry (incr[a+b]≡incr[a]+b ((Itℕ (incrementℤ y) incrementℤ x)) {z})) (congruence incrementℤ (assocℤ+ (pos (suc (x))) y {z}))
assocℤ+ (neg zero) y {z} =  (propertySymmetry (idℤ[a+b]≡idℤa+b (y) (z)))
assocℤ+ (neg (suc zero)) y = propertySymmetry (decr[a+b]≡decr[a]+b y)
assocℤ+ (neg (suc (suc x))) y {z} = propertyTransitivity (propertySymmetry (decr[a+b]≡decr[a]+b (neg (suc x) + y) {z})) (congruence decrementℤ (assocℤ+ (neg (suc (x))) y {z}))
