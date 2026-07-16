module Defunctionalized.Calculus.Shallow where

open import Data.Nat hiding (suc)
open import Data.Product renaming (proj₁ to π₁; proj₂ to π₂)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Basic
open import Context

import Defunctionalized.Calculus.Syntax as S

open S using (LCon; LVar; ●; _⨾_)

private variable
  Γ Γ' Γ'' Δ Δ' Δ'' : Con
  A A' B B' C C' : Ty 
  D D' D'' : LCon

{- Shallow embedding of DLC -}

⟦_⟧T : Ty → Set
⟦ One ⟧T = ⊤
⟦ Nat ⟧T = ℕ
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T
⟦ A ⊗ B ⟧T = ⟦ A ⟧T × ⟦ B ⟧T

⟦_⟧Γ : Con → Set
⟦ · ⟧Γ = ⊤
⟦ Γ ∷ A ⟧Γ = ⟦ Γ ⟧Γ × ⟦ A ⟧T

record ~Π (Γ : Con) (A : Ty) : Set where
  constructor ~λ
  field
    ~fun : ⟦ Γ ⟧Γ → ⟦ A ⟧T
open ~Π

⟦_⟧D : LCon → Set
Tm : 
-- ⟦_⟧ : S.Tm D Γ A → ⟦ D ⟧D → ⟦ Γ ⟧Γ → Set

⟦ ● ⟧D = ⊤
⟦ D ⨾ t ⟧D = {!   !}


