{-# OPTIONS --type-in-type #-}
module pred-logic.def where

open import type-variables.type-vars

-- Propositions as types
prop = Set

-- Datatype: Equality 
data _≡_ : {A : Set} → A → A → prop where
  refl : {a : A} → a ≡ a

-- Record Datatype: Equivalence Relation
record isEqRel (_~_ : A → A → prop) : prop where
  field
    reflexive : {a : A} → a ~ a
    symmetric : {a b : A} → (a ~ b) → (b ~ a)
    transitive : {a b c : A} → (a ~ b) → (b ~ c) → (a ~ c)