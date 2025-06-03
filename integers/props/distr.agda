module integers.props.distr where

open import naturals.def
open import naturals.ops renaming (_+_ to _ℕ+_; _*_ to _*ℕ_)


open import pred-logic.def
open import pred-logic.props

open import integers.def
open import integers.ops

open import integers.props.add.neutr
open import integers.props.add.inv
open import integers.props.add.comm
open import integers.props.add.assoc

open import integers.props.lemmas.incr-decr
open import integers.props.lemmas.incr-decr-idZ
open import integers.props.lemmas.idZ
open import integers.props.lemmas.negZ

-- Lemmas for distributive laws.

-- a)
distrIncrOverProducts : (x y : ℤ) → ((incrementℤ x) * y) ≡ (y + (x * y))
distrIncrOverProducts (pos x) y = refl
distrIncrOverProducts (neg zero) y = refl
distrIncrOverProducts (neg (suc zero)) y = propertyTransitivity (propertyTransitivity (propertyTransitivity (propertySymmetry (propertyTransitivity (rightNeutr+ℤ+ (negateℤ y + y)) (propertyTransitivity (idℤ+≡+ (negateℤ y) {y}) (leftAddInvℤ+ y)))) (assocℤ+ (negateℤ y) (y) {pos zero})) (congruence (negateℤ y +_) (distrIncrOverProducts (neg zero) y))) (propertyTransitivity (propertySymmetry (assocℤ+ (negateℤ y) (y) {pos zero})) (propertySymmetry (propertyTransitivity (propertySymmetry (assocℤ+ (y) (negateℤ y) {pos zero})) (congruence (_+ pos zero) (commℤ+ (y) {negateℤ y})))))
distrIncrOverProducts (neg (suc (suc zero))) y = propertyTransitivity (propertyTransitivity (congruence (negateℤ y +_) refl) (congruence (negateℤ y +_) (distrIncrOverProducts (neg (suc (zero))) y))) (propertyTransitivity (propertySymmetry (assocℤ+ (negateℤ y) (y) {negateℤ y + (neg zero * y)})) (propertyTransitivity (congruence (_+ (negateℤ y + (neg zero * y))) (commℤ+ (negateℤ y) {y})) (assocℤ+ (y) (negateℤ y) {negateℤ y + (neg zero * y)})))
distrIncrOverProducts (neg (suc (suc (suc x)))) y = propertyTransitivity (congruence (negateℤ y +_) (distrIncrOverProducts (neg (suc (suc (x)))) y)) (propertySymmetry (propertyTransitivity (propertySymmetry (assocℤ+ (y) (negateℤ y) {negateℤ y + (negateℤ y + (neg x * y))})) (propertySymmetry (propertyTransitivity (propertySymmetry (assocℤ+ (negateℤ y) (y) {negateℤ y + (negateℤ y + (neg x * y))})) (congruence (_+ (negateℤ y + (negateℤ y + (neg x * y)))) (commℤ+ (negateℤ y) {y}))))))

-- b)
rightDistLemma : (a : ℤ) {z : ℤ} → ((decrementℤ a) * z) ≡ (negateℤ z + (a * z))
rightDistLemma (pos zero) = refl
-- pos 3 * 2 == 2 + (2 * 2)
rightDistLemma (pos (suc a)) {z} = propertyTransitivity (propertyTransitivity (propertyTransitivity (incr[decr[posa]*z]≡a*z a {z}) (distrIncrOverProducts (decrementℤ (pos a)) z)) (congruence (z +_) (rightDistLemma (pos a) {z}))) (propertyTransitivity (propertySymmetry (assocℤ+ z (negateℤ z) {pos a * z})) (propertyTransitivity (congruence (_+ (pos a * z)) (commℤ+ (z) {negateℤ z})) (assocℤ+ (negateℤ z) (z) {pos a * z})))
rightDistLemma (neg zero) = refl
rightDistLemma (neg (suc a)) = refl

-- c)
a+b≡suca+sucb : (z : ℕ) → (neg z + pos z) ≡ (neg (suc z) + pos (suc z))
a+b≡suca+sucb zero = refl
a+b≡suca+sucb (suc z) = propertyTransitivity (propertyTransitivity (propertySymmetry (a+b≡suca+sucb z)) (a+b≡suca+sucb z)) (propertySymmetry (decr[a+b]≡a+decr[b] (neg (suc z)) {pos (suc (suc z))}))

-- d)
possucnegsucidℤ : (z : ℕ) → (pos (suc z) + neg (suc z)) ≡ (pos z + idℤ (neg z))
possucnegsucidℤ zero = refl
possucnegsucidℤ (suc (z)) = propertyTransitivity (incr[a+b]≡incr[a]+b (pos (suc z)) {neg (suc (suc z))}) (incr[a+b]≡a+incr[b] (pos (suc z)) {neg (suc (suc z))})

-- e)
z+negℤ≡poszero : (z : ℤ) → (z + (negateℤ z + pos zero)) ≡ pos zero
z+negℤ≡poszero (pos zero) = refl
z+negℤ≡poszero (pos (suc z)) = propertyTransitivity (propertyTransitivity (propertySymmetry (assocℤ+ (pos (suc z)) (neg (suc z)) {pos zero})) (propertySymmetry (propertyTransitivity (propertySymmetry (assocℤ+ (pos z) (idℤ (neg z)) {pos zero})) (propertySymmetry (congruence (_+ pos zero) ( (possucnegsucidℤ z))))))) (z+negℤ≡poszero (pos (z)))
z+negℤ≡poszero (neg zero) = refl
z+negℤ≡poszero (neg (suc z)) = propertyTransitivity (propertyTransitivity (propertySymmetry (assocℤ+ (neg (suc z)) (pos (suc z)) {pos zero})) (propertySymmetry (propertyTransitivity (propertySymmetry (assocℤ+ (neg z) (pos z) {pos zero})) (congruence (_+ (pos zero)) (a+b≡suca+sucb z))))) (z+negℤ≡poszero (neg (z)))

-- f)
rightDistrL : (x : ℕ) (y z : ℤ) → (negateℤ z + ((neg x + y) * z)) ≡ ((neg (suc x) + y) * z)
rightDistrL zero (pos zero) z = refl
rightDistrL zero (pos (suc zero)) z = propertyTransitivity (propertyTransitivity (propertySymmetry (propertyTransitivity (commℤ+ (z) {negateℤ z + (pos zero * z)}) (propertyTransitivity (assocℤ+ (negateℤ z) (pos zero * z) {z}) (congruence (negateℤ z +_) (commℤ+ (pos zero * z) {z}))))) (congruence (z +_) (rightDistrL zero (pos (zero)) z))) (z+negℤ≡poszero z)
rightDistrL zero (pos (suc (suc y))) z = propertyTransitivity (propertySymmetry (propertyTransitivity (propertySymmetry (assocℤ+ (z) (negateℤ z) {z + (pos y * z)})) (propertySymmetry (propertyTransitivity (propertySymmetry (assocℤ+ (negateℤ z) z {z + (pos y * z)})) (congruence (_+ (z + (pos y * z))) (commℤ+ (negateℤ z) {z})))))) (congruence (z +_) (rightDistrL zero (pos (suc (y))) z))
rightDistrL zero (neg zero) z = refl
rightDistrL zero (neg (suc y)) z = refl
rightDistrL (suc x) y z = propertyTransitivity (congruence ((negateℤ z) +_) (propertySymmetry (rightDistrL x y z))) (propertyTransitivity (congruence (negateℤ z +_) (rightDistrL x y z)) (propertySymmetry (rightDistLemma (neg (suc x) + y) {z})))


-- Main Proofs

-- Property: Left Distributive Law
leftDistrℤ : (x y : ℤ) {z : ℤ} → (x * (y + z)) ≡ ((x * y) + (x * z))
leftDistrℤ (pos zero) y = refl
leftDistrℤ (pos (suc x)) y {z} = propertyTransitivity (congruence ((y + z) +_) (leftDistrℤ (pos (x)) y {z})) (propertyTransitivity (assocℤ+ (y) (z) {(pos x * y) + (pos x * z)}) (propertyTransitivity (commℤ+ (y) {z + ((pos x * y) + (pos x * z))}) (propertyTransitivity (propertyTransitivity (commℤ+ (z + ((pos x * y) + (pos x * z))) {y}) (congruence (y +_) (propertySymmetry (propertyTransitivity (commℤ+ (pos x * y) {z + (pos x * z)}) (propertyTransitivity (assocℤ+ (z) (pos x * z) {pos x * y}) (congruence (z +_) (commℤ+ (pos x * z) {pos x * y}))))))) (propertySymmetry (assocℤ+ (y) (pos x * y) {z + (pos x * z)})))))
leftDistrℤ (neg zero) y = refl
leftDistrℤ (neg (suc x)) y {z} = propertyTransitivity (congruence (negateℤ (y + z) +_ ) (leftDistrℤ (neg (x)) y {z})) (propertySymmetry (propertyTransitivity (assocℤ+ (negateℤ y) (neg x * y) {negateℤ z + (neg x * z)}) (propertySymmetry (propertyTransitivity (commℤ+ (negateℤ (y + z)) {(neg x * y) + (neg x * z)}) (propertySymmetry (propertyTransitivity (commℤ+ (negateℤ y) {(neg x * y) + (negateℤ z + (neg x * z))}) (propertyTransitivity (assocℤ+ (neg x * y) (negateℤ z + (neg x * z)) {negateℤ y}) (propertySymmetry (propertyTransitivity (assocℤ+ (neg x * y) (neg x * z) {negateℤ (y + z)}) (congruence ((neg x * y) +_ ) (propertySymmetry (propertyTransitivity (assocℤ+ (negateℤ z) (neg x * z) {negateℤ y}) (propertyTransitivity (commℤ+ (negateℤ z) {(neg x * z) + negateℤ y}) (propertyTransitivity (assocℤ+ (neg x * z) (negateℤ y) {negateℤ z}) (congruence ((neg x * z) +_ ) (propertySymmetry (negateℤ[x+y]≡negℤx+negℤy y {z})))))))))))))))))


-- Property: Right Distributive Law
rightDistrℤ : (x y : ℤ) {z : ℤ} → ((x + y) * z) ≡ ((x * z) + (y * z))
rightDistrℤ (pos zero) y {z} = propertySymmetry (idℤ[AxB]≡idℤAxB y z) 
rightDistrℤ (pos (suc x)) y {z} = propertyTransitivity (propertyTransitivity (congruence (_* z) (propertySymmetry (incr[a+b]≡incr[a]+b (pos x) {y}))) (distrIncrOverProducts (pos x + y) z)) ((propertyTransitivity (congruence (z +_ ) (rightDistrℤ (pos (x)) y {z})) (propertySymmetry (assocℤ+ z (pos x * z) {y * z}))))
rightDistrℤ (neg zero) y {z} = propertySymmetry (idℤ[AxB]≡idℤAxB y z)
rightDistrℤ (neg (suc x)) y {z} = propertyTransitivity (propertyTransitivity (propertySymmetry (rightDistrL x y z)) (congruence (negateℤ z +_) (rightDistrℤ (neg (x)) y {z}))) (propertySymmetry (assocℤ+ (negateℤ z) (neg x * z) {y * z}))
