module integers.props.lemmas.incr-decr-idZ where

open import naturals.def

open import pred-logic.def
open import pred-logic.props

open import integers.def
open import integers.ops

-- Lemmas related to idℤ, incrementℤ and decrementℤ

-- a)
idx1-2 : (y : ℤ) → (idℤ y) ≡ (idℤ (idℤ y))
idx1-2 (pos y) = refl
idx1-2 (neg zero) = refl
idx1-2 (neg (suc y)) = refl

-- b)
idℤnegx≡negsucx : (x : ℕ) → idℤ (neg x) ≡ incrementℤ (neg (suc x))
idℤnegx≡negsucx zero = refl
idℤnegx≡negsucx (suc x) = refl

-- c)
decrIncrℤ≡ : (x : ℤ) → decrementℤ (incrementℤ x) ≡ idℤ x
decrIncrℤ≡ (pos x) = refl
decrIncrℤ≡ (neg zero) = refl
decrIncrℤ≡ (neg (suc zero)) = refl
decrIncrℤ≡ (neg (suc (suc x))) = refl

-- d)
idℤIncrSuc≡decridℤ : (x : ℕ) → idℤ (incrementℤ (neg (suc x))) ≡ decrementℤ (idℤ (incrementℤ (neg x)))
idℤIncrSuc≡decridℤ zero = refl
idℤIncrSuc≡decridℤ (suc zero) = refl
idℤIncrSuc≡decridℤ (suc (suc x)) = refl

-- e)
idℤ-Incr≡Incr-idℤ : (a : ℤ) → idℤ (incrementℤ a) ≡ incrementℤ (idℤ a)
idℤ-Incr≡Incr-idℤ (pos x) = refl
idℤ-Incr≡Incr-idℤ (neg zero) = refl
idℤ-Incr≡Incr-idℤ (neg (suc x)) = propertyTransitivity (idℤIncrSuc≡decridℤ x) (propertyTransitivity (congruence decrementℤ (idℤ-Incr≡Incr-idℤ (neg x))) (propertyTransitivity (decrIncrℤ≡ (idℤ (neg x))) (propertyTransitivity (propertySymmetry (idx1-2 (neg x))) (idℤnegx≡negsucx x))))

-- f)
incrℤidℤ≡incrℤ : (x : ℤ) → incrementℤ (idℤ x) ≡ incrementℤ x
incrℤidℤ≡incrℤ (pos x) = refl
incrℤidℤ≡incrℤ (neg zero) = refl
incrℤidℤ≡incrℤ (neg (suc x)) = refl

-- g)
idℤincrℤ≡incrℤ : (x : ℤ) → idℤ (incrementℤ x) ≡ incrementℤ x
idℤincrℤ≡incrℤ (pos x) = refl
idℤincrℤ≡incrℤ (neg zero) = refl
idℤincrℤ≡incrℤ (neg (suc zero)) = refl
idℤincrℤ≡incrℤ (neg (suc (suc x))) = refl

-- h)
idℤDecr≡Decr : (x : ℤ) → idℤ (decrementℤ x) ≡ decrementℤ x
idℤDecr≡Decr (pos zero) = refl
idℤDecr≡Decr (pos (suc x)) = refl
idℤDecr≡Decr (neg x) = refl

-- i)
idℤ-Decr≡Decr-idℤ : (a : ℤ) → idℤ (decrementℤ a) ≡ decrementℤ (idℤ a)
idℤ-Decr≡Decr-idℤ (pos zero) = refl
idℤ-Decr≡Decr-idℤ (pos (suc x)) = refl
idℤ-Decr≡Decr-idℤ (neg zero) = refl
idℤ-Decr≡Decr-idℤ (neg (suc x)) = refl

-- j)
incrDecrℤ≡ : (x : ℤ) → incrementℤ (decrementℤ x) ≡ idℤ x
incrDecrℤ≡ (pos zero) = refl
incrDecrℤ≡ (pos (suc x)) = refl
incrDecrℤ≡ (neg zero) = refl
incrDecrℤ≡ (neg (suc x)) = refl

-- k)
decrIncr≡IncrDecr : (x : ℤ) → decrementℤ (incrementℤ x) ≡ incrementℤ (decrementℤ x)
decrIncr≡IncrDecr (pos zero) = refl
decrIncr≡IncrDecr (pos (suc x)) = refl
decrIncr≡IncrDecr (neg zero) = refl
decrIncr≡IncrDecr (neg (suc zero)) = refl
decrIncr≡IncrDecr (neg (suc (suc x))) = refl

-- l)
Decridℤ≡Decr : (x : ℤ) → (decrementℤ (idℤ x)) ≡ decrementℤ x
Decridℤ≡Decr (pos zero) = refl
Decridℤ≡Decr (pos (suc x)) = refl
Decridℤ≡Decr (neg zero) = refl
Decridℤ≡Decr (neg (suc x)) = refl
