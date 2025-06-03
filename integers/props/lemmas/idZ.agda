module integers.props.lemmas.idZ where

open import naturals.def
open import naturals.ops renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import pred-logic.def
open import pred-logic.props

open import integers.def
open import integers.ops
open import integers.props.lemmas.incr-decr-idZ

-- a)
idℤ+≡+ : (x : ℤ) {y : ℤ} → (idℤ (x + y)) ≡ (x + y)
idℤ+≡+ (pos zero) {y} = propertySymmetry (idx1-2 y)
idℤ+≡+ (pos (suc zero)) {y} = idℤincrℤ≡incrℤ y
idℤ+≡+ (pos (suc (suc x))) {y} = idℤincrℤ≡incrℤ (Itℕ (incrementℤ y) incrementℤ x)
idℤ+≡+ (neg zero) {y} = propertySymmetry (idx1-2 y)
idℤ+≡+ (neg (suc zero)) {y} = idℤDecr≡Decr y
idℤ+≡+ (neg (suc (suc x))) {y} = idℤDecr≡Decr (Itℕ (decrementℤ y) decrementℤ x)

-- b)
idℤ[a+b]≡idℤa+b : (a b : ℤ) → idℤ (a + b) ≡ ((idℤ a) + b)
idℤ[a+b]≡idℤa+b (pos a) b = idℤ+≡+ (pos a) {b}
idℤ[a+b]≡idℤa+b (neg zero) b = propertySymmetry (idx1-2 b)
idℤ[a+b]≡idℤa+b (neg (suc a)) (pos b) = idℤ+≡+ (neg (suc a)) {pos b}
idℤ[a+b]≡idℤa+b (neg (suc a)) (neg b) = idℤ+≡+ (neg (suc a)) {neg b}

-- c)
idℤ[a+b]≡a+idℤb : (a b : ℤ) → idℤ (a + b) ≡ (a + (idℤ b))
idℤ[a+b]≡a+idℤb (pos zero) b = refl
idℤ[a+b]≡a+idℤb (pos (suc a)) (pos b) = idℤ+≡+ (pos (suc a)) {pos b}
idℤ[a+b]≡a+idℤb (pos (suc a)) (neg zero) = idℤ+≡+ (pos (suc a)) {pos 0}
idℤ[a+b]≡a+idℤb (pos (suc a)) (neg (suc b)) = idℤ+≡+ (pos (suc a)) {neg (suc b)}
idℤ[a+b]≡a+idℤb (neg zero) b = refl
idℤ[a+b]≡a+idℤb (neg (suc a)) (pos b) = idℤ+≡+ (neg (suc a)) {pos b}
idℤ[a+b]≡a+idℤb (neg (suc a)) (neg zero) = idℤ+≡+ (neg (suc a)) {pos 0}
idℤ[a+b]≡a+idℤb (neg (suc a)) (neg (suc b)) = idℤ+≡+ (neg (suc a)) {neg (suc (b))}

-- d)
idℤ[a+b]≡idℤa+idℤb : (x y : ℤ) → (idℤ x + idℤ y) ≡ idℤ (x + y)
idℤ[a+b]≡idℤa+idℤb (pos x) y = propertySymmetry (idℤ[a+b]≡a+idℤb (pos x) y)
idℤ[a+b]≡idℤa+idℤb (neg zero) y = refl
idℤ[a+b]≡idℤa+idℤb (neg (suc x)) y = propertySymmetry (idℤ[a+b]≡a+idℤb (neg (suc x)) y)

-- e)
idℤ[AxB]≡idℤAxB : (a b : ℤ) → idℤ (a * b) ≡ ((idℤ a) * b)
idℤ[AxB]≡idℤAxB (pos zero) b = refl
idℤ[AxB]≡idℤAxB (pos (suc a)) b = propertyTransitivity (idℤ[a+b]≡a+idℤb b (pos a * b)) (congruence (b +_) (idℤ[AxB]≡idℤAxB (pos (a)) b))
idℤ[AxB]≡idℤAxB (neg zero) (pos b) = refl
idℤ[AxB]≡idℤAxB (neg (suc a)) (pos b) = idℤ+≡+ (idℤ (neg b)) {neg a * pos b}
idℤ[AxB]≡idℤAxB (neg zero) (neg b) = refl
idℤ[AxB]≡idℤAxB (neg (suc a)) (neg b) = idℤ+≡+ (pos b) {neg a * neg b}

-- f)
idℤa*b≡a*b : (a b : ℤ) → idℤ (a * b) ≡ (a * b)
idℤa*b≡a*b (pos zero) b = refl
idℤa*b≡a*b (pos (suc a)) b = idℤ+≡+ b {pos a * b}
idℤa*b≡a*b (neg zero) b = refl
idℤa*b≡a*b (neg (suc a)) b = idℤ+≡+ (negateℤ b) {neg a * b}
