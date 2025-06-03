module integers.ops where

open import naturals.def
open import naturals.ops renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import integers.def

{- (Old) Operation: Addition over ℤ
_+_ : ℤ → ℤ → ℤ
pos x + pos y = pos (x +ℕ y)
pos x + neg zero = pos x
pos zero + neg (suc y) = neg (suc y)
pos (suc x) + neg (suc y) = idℤ ((pos x) + (neg y))
neg x + pos zero = idℤ (neg x)
neg zero + pos (suc y) = pos (suc y)
neg (suc x) + pos (suc y) = idℤ ((neg x) + (pos y))
neg zero + neg y = idℤ (neg y)
neg (suc x) + neg zero = neg (suc x)
neg (suc x) + neg (suc y) = neg ((suc x) +ℕ (suc y)) -}


-- Operation: Addition over ℤ
_+_ : ℤ → ℤ → ℤ
pos zero + y = idℤ y 
pos (suc x) + y = Itℕ (incrementℤ y) (incrementℤ) (x) 
neg zero + y = idℤ y
neg (suc x) + y = Itℕ (decrementℤ y) (decrementℤ) (x)

-- Operation: Subtraction over ℤ 
_-_ : ℤ → ℤ → ℤ
x - y = x + (negateℤ y)

-- Operation: Multiplication over ℤ
_*_ : ℤ → ℤ → ℤ
pos zero * y = pos zero
pos (suc x) * y = y + ((pos x) * y)
neg zero * y = pos zero
neg (suc x) * y = (negateℤ y) + ((neg x) * y)

