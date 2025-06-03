module integers.props.lemmas.negZ where

open import naturals.def
open import naturals.ops renaming (_+_ to _ℕ+_; _*_ to _*ℕ_)


open import pred-logic.def
open import pred-logic.props

open import integers.def
open import integers.ops

open import integers.props.lemmas.incr-decr
open import integers.props.lemmas.incr-decr-idZ
open import integers.props.lemmas.idZ

-- a)
negIncr≡decrNeg : (a : ℤ) → negateℤ (incrementℤ a) ≡ decrementℤ (negateℤ a)
negIncr≡decrNeg (pos zero) = refl
negIncr≡decrNeg (pos (suc x)) = refl
negIncr≡decrNeg (neg zero) = refl
negIncr≡decrNeg (neg (suc zero)) = refl
negIncr≡decrNeg (neg (suc (suc x))) = refl

-- b)
negDecr≡incrNeg : (a : ℤ) → negateℤ (decrementℤ a) ≡ incrementℤ (negateℤ a)
negDecr≡incrNeg (pos zero) = refl
negDecr≡incrNeg (pos (suc zero)) = refl
negDecr≡incrNeg (pos (suc (suc a))) = refl
negDecr≡incrNeg (neg a) = refl

-- c)
negateℤ[x+y]≡negℤx+negℤy : (x : ℤ) {y : ℤ}  → (negateℤ (x + y)) ≡ (negateℤ x + negateℤ y)
negateℤ[x+y]≡negℤx+negℤy (pos zero) {pos y} = idx1-2 (neg y)
negateℤ[x+y]≡negℤx+negℤy (pos zero) {neg zero} = refl
negateℤ[x+y]≡negℤx+negℤy (pos zero) {neg (suc y)} = refl
negateℤ[x+y]≡negℤx+negℤy (pos (suc zero)) {pos zero} = refl
negateℤ[x+y]≡negℤx+negℤy (pos (suc (suc x))) {pos zero} = propertyTransitivity (negIncr≡decrNeg (pos (suc x) + pos zero)) (congruence decrementℤ (negateℤ[x+y]≡negℤx+negℤy (pos (suc (x))) {pos zero}))
negateℤ[x+y]≡negℤx+negℤy (pos (suc zero)) {pos (suc y)} = refl
negateℤ[x+y]≡negℤx+negℤy (pos (suc (suc x))) {pos (suc y)} = propertyTransitivity (negIncr≡decrNeg (pos (suc x) + pos (suc y))) (congruence decrementℤ (negateℤ[x+y]≡negℤx+negℤy (pos (suc (x))) {pos (suc y)}))
negateℤ[x+y]≡negℤx+negℤy (pos (suc zero)) {neg zero} = refl
negateℤ[x+y]≡negℤx+negℤy (pos (suc (suc x))) {neg zero} = propertyTransitivity (negIncr≡decrNeg (pos (suc x) + pos zero)) (congruence decrementℤ (negateℤ[x+y]≡negℤx+negℤy (pos (suc (x))) {neg zero}))
negateℤ[x+y]≡negℤx+negℤy (pos (suc zero)) {neg (suc zero)} = refl
negateℤ[x+y]≡negℤx+negℤy (pos (suc zero)) {neg (suc (suc y))} = refl
negateℤ[x+y]≡negℤx+negℤy (pos (suc (suc x))) {neg (suc zero)} = propertyTransitivity (negIncr≡decrNeg (pos (suc x) + neg 1)) (congruence decrementℤ (negateℤ[x+y]≡negℤx+negℤy (pos (suc (x))) {neg (suc zero)}))
negateℤ[x+y]≡negℤx+negℤy (pos (suc (suc x))) {neg (suc (suc y))} = propertyTransitivity (negIncr≡decrNeg (Itℕ (neg (suc y)) incrementℤ x)) (congruence decrementℤ (negateℤ[x+y]≡negℤx+negℤy (pos (suc (x))) {neg (suc (suc y))}))
negateℤ[x+y]≡negℤx+negℤy (neg zero) {pos y} = idx1-2 (neg y)
negateℤ[x+y]≡negℤx+negℤy (neg zero) {neg zero} = refl
negateℤ[x+y]≡negℤx+negℤy (neg zero) {neg (suc y)} = refl
negateℤ[x+y]≡negℤx+negℤy(neg (suc zero)) {pos zero} = refl
negateℤ[x+y]≡negℤx+negℤy (neg (suc (suc x))) {pos zero} = propertyTransitivity (negDecr≡incrNeg (neg (suc x) + pos zero)) (congruence incrementℤ (negateℤ[x+y]≡negℤx+negℤy (neg (suc (x))) {pos zero}))
negateℤ[x+y]≡negℤx+negℤy (neg (suc zero)) {pos (suc zero)} = refl
negateℤ[x+y]≡negℤx+negℤy (neg (suc (suc x))) {pos (suc zero)} = propertyTransitivity (negDecr≡incrNeg (neg (suc x) + pos 1)) (congruence incrementℤ (negateℤ[x+y]≡negℤx+negℤy (neg (suc (x))) {pos (suc zero)}))
negateℤ[x+y]≡negℤx+negℤy (neg (suc zero)) {pos (suc (suc y))} = refl
negateℤ[x+y]≡negℤx+negℤy (neg (suc (suc x))) {pos (suc (suc y))} = propertyTransitivity (negDecr≡incrNeg (Itℕ (pos (suc y)) decrementℤ x)) (congruence incrementℤ (negateℤ[x+y]≡negℤx+negℤy (neg (suc (x))) {pos (suc (suc y))}))
negateℤ[x+y]≡negℤx+negℤy (neg (suc zero)) {neg zero} = refl
negateℤ[x+y]≡negℤx+negℤy (neg (suc (suc x))) {neg zero} = propertyTransitivity (negDecr≡incrNeg (Itℕ (neg 1) decrementℤ x)) (congruence incrementℤ (negateℤ[x+y]≡negℤx+negℤy (neg (suc (x))) {neg zero}))
negateℤ[x+y]≡negℤx+negℤy (neg (suc zero)) {neg (suc y)} = refl
negateℤ[x+y]≡negℤx+negℤy (neg (suc (suc x))) {neg (suc y)} = propertyTransitivity (negDecr≡incrNeg (Itℕ (neg (suc (suc y))) decrementℤ x)) (congruence incrementℤ (negateℤ[x+y]≡negℤx+negℤy (neg (suc (x))) {neg (suc y)}))

-- d)
negIdℤIdℤ≡IdℤnegIdℤ+ : (a : ℤ) → negateℤ (idℤ (a)) ≡ idℤ (negateℤ (a))
negIdℤIdℤ≡IdℤnegIdℤ+ (pos a) = idx1-2 (neg a)
negIdℤIdℤ≡IdℤnegIdℤ+ (neg zero) = refl
negIdℤIdℤ≡IdℤnegIdℤ+ (neg (suc a)) = refl

-- e)
negIdℤneg≡pos : (b : ℕ) → negateℤ (idℤ (neg b)) ≡ pos b
negIdℤneg≡pos zero = refl
negIdℤneg≡pos (suc b) = refl

-- f)
negℤ[a*b]≡[negℤa]*b : (a : ℤ) {b : ℤ} → negateℤ (a * b) ≡ ((negateℤ a) * b)
negℤ[a*b]≡[negℤa]*b (pos zero) = refl
negℤ[a*b]≡[negℤa]*b (pos (suc zero)) {b} = propertyTransitivity (negateℤ[x+y]≡negℤx+negℤy b {pos zero}) (congruence (negateℤ b +_) (negℤ[a*b]≡[negℤa]*b (pos (zero)) {b}))
negℤ[a*b]≡[negℤa]*b (pos (suc (suc a))) {b} = propertyTransitivity (negateℤ[x+y]≡negℤx+negℤy b {b + (pos a * b)}) (congruence (negateℤ b +_) (negℤ[a*b]≡[negℤa]*b (pos (suc (a))) {b}))
negℤ[a*b]≡[negℤa]*b (neg zero) {b} = refl
negℤ[a*b]≡[negℤa]*b (neg (suc a)) {pos b} = propertyTransitivity (propertyTransitivity (negateℤ[x+y]≡negℤx+negℤy (idℤ (neg b)) {neg a * pos b}) (congruence (_+ negateℤ (neg a * pos b)) (negIdℤneg≡pos b))) (congruence (pos b +_) (negℤ[a*b]≡[negℤa]*b (neg (a)) {pos b}))
negℤ[a*b]≡[negℤa]*b (neg (suc a)) {neg zero} = propertyTransitivity (negIdℤIdℤ≡IdℤnegIdℤ+ (neg a * neg zero)) (congruence idℤ (negℤ[a*b]≡[negℤa]*b (neg (a)) {neg zero}))
negℤ[a*b]≡[negℤa]*b (neg (suc a)) {neg (suc b)} = propertyTransitivity (negateℤ[x+y]≡negℤx+negℤy (pos (suc b)) {neg a * neg (suc b)}) (congruence (neg (suc b) +_) (negℤ[a*b]≡[negℤa]*b (neg (a)) {neg (suc b)}))
