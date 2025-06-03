module integers.def where

open import type-variables.bool

open import naturals.def

-- Definition : Integers (ℤ)
record ℤ : Set where
  constructor ⟨_⟩
  field
    sign      : Bool
    magnitude : ℕ

open ℤ public

-- Pattern synonyms to improve readability
pattern pos x = ⟨ true ⟩ x
pattern neg x = ⟨ false ⟩ x

-- Alternate approach.
{- data Int : Set where
  pos : ℕ → Int
  negsuc : ℕ → Int
-}

-- Core Definition Functions

-- Normalization function to eliminate neg zero.
idℤ : ℤ → ℤ
idℤ (pos x) = pos x
idℤ (neg zero) = pos zero
idℤ (neg (suc x)) = neg (suc x)

-- Increment and Decrement functions.
incrementℤ : ℤ → ℤ
incrementℤ (pos x) = pos (suc x)
incrementℤ (neg zero) = pos (suc zero)
incrementℤ (neg (suc zero)) = pos zero
incrementℤ (neg (suc (suc x))) = neg (suc x)

decrementℤ : ℤ → ℤ
decrementℤ (pos zero) = neg (suc zero)
decrementℤ (pos (suc x)) = pos x
decrementℤ (neg x) = neg (suc x)

-- Function to flip the sign of an integer
negateℤ : ℤ → ℤ
negateℤ (pos x) = idℤ (neg x)
negateℤ (neg x) = pos x

-- Recursor for ℤ
Recℤ : {A : Set} → (ℕ → A) → (ℕ → A) → ℤ → A
Recℤ p ns (⟨ true ⟩ mag) = p mag
Recℤ p ns (⟨ false ⟩ mag) = ns mag


