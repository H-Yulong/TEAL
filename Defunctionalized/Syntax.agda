module Defunctionalized.Syntax where

open import Data.Nat
open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Relation.Binary.PropositionalEquality 

open import Basic
open import Context

{- Pre-syntax -}
mutual
  data Instr : Set where
    -- Core language
    pop swap app unit : Instr
    var st : ∀{Γ A} → Var Γ A → Instr
    clo : ℕ → Is → Instr
    -- Natural numbers
    lit : ℕ → Instr
    suc add mult : Instr
    rec : Is → Is → Instr 

  data Is : Set where
    ret : Is
    _⨾_ : Instr → Is → Is





