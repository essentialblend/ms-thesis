module type-variables.bool where

-- Definition: Boolean

data Bool : Set where
  true  : Bool
  false : Bool

open Bool public