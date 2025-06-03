module naturals.ops where

open import type-variables.bool
open import type-variables.type-vars

open import naturals.def

-- Various operations over ℕ.

-- Operation: Addition
_+_ : ℕ → ℕ → ℕ
zero + n    = n
(suc m) + n = suc (m + n) 

-- Operation: Multiplication
_*_ : ℕ → ℕ → ℕ
zero * n    = zero
(suc m) * n = n + (m * n)

-- Operation: Exponentiation
_↑_ : ℕ → ℕ → ℕ
m ↑ zero    = suc zero
m ↑ (suc n) = m * (m ↑ n)

-- Operation: C-Off Subtraction
_-ℕ_ : ℕ → ℕ → ℕ
zero -ℕ _ = zero
suc x -ℕ zero = suc x
suc x -ℕ suc y = x -ℕ y

-- Operation: Less than
_<ℕ_ : ℕ → ℕ → Bool
zero <ℕ zero   = false
zero <ℕ suc y  = true
suc x <ℕ zero  = false
suc x <ℕ suc y = x <ℕ y

-- Operation: Less than or Equal to
_<=ℕ_ : ℕ → ℕ → Bool
zero <=ℕ zero   = true
zero <=ℕ suc y  = true
suc x <=ℕ zero  = false
suc x <=ℕ suc y = x <=ℕ y

-- Operation: Greater than
_>ℕ_ : ℕ → ℕ → Bool
zero >ℕ zero   = false
zero >ℕ suc y  = false
suc x >ℕ zero  = true
suc x >ℕ suc y = x >ℕ y

-- Operation: Greater than or Equal to
_>=ℕ_ : ℕ → ℕ → Bool
zero >=ℕ zero   = true
zero >=ℕ suc y  = false
suc x >=ℕ zero  = true
suc x >=ℕ suc y = x >=ℕ y

-- Iterator over ℕ
Itℕ : P → (P → P) → ℕ → P
Itℕ z s zero = z
Itℕ z s (suc n) = s (Itℕ z s n)
