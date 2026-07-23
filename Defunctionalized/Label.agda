module Defunctionalized.Label where

open import Basic
open import Context

infixl 10 _∷<_⊢_>

{- Labels, with just the type information -}

data LCon : Set where
  ● : LCon
  _∷<_⊢_> : LCon → Con → Ty → LCon

data LVar : LCon → Con → Ty → Set where
  ℓ₀ : ∀{D Δ A} → LVar (D ∷< Δ ⊢ A >) Δ A
  ℓs : ∀{D Δ A Δ' A'} → LVar D Δ A → LVar (D ∷< Δ' ⊢ A' >) Δ A

{- LCon renamings -}
LRen : LCon → LCon → Set
LRen D D' = ∀{Γ A} → LVar D Γ A → LVar D' Γ A



