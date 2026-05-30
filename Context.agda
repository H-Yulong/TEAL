module Context where

open import Basic
open import Data.Nat

infixr 30 _⇒_
infixl 20 _∷_
infixl 30 _⊗_

data Ty : Set where
  One : Ty
  Nat : Ty
  _⇒_ : Ty → Ty → Ty
  _⊗_ : Ty → Ty → Ty

data Con : Set where
  · : Con
  _∷_ : Con → Ty → Con

data Var : Con → Ty → Set where
  v₀ : ∀{Γ A} → Var (Γ ∷ A) A
  vs : ∀{Γ A B} → Var Γ A → Var (Γ ∷ B) A 

v₁ : ∀{Γ A B} → Var (Γ ∷ A ∷ B) A
v₁ = vs v₀

v₂ : ∀{Γ A B C} → Var (Γ ∷ A ∷ B ∷ C) A
v₂ = vs (vs v₀)

v₃ : ∀{Γ A B C D} → Var (Γ ∷ A ∷ B ∷ C ∷ D) A
v₃ = vs (vs (vs v₀))

{- Renamings -}
Ren : Con → Con → Set
Ren Γ Δ = ∀{A} → Var Γ A → Var Δ A

ext : ∀{Γ Δ A} → Ren Γ Δ → Ren (Γ ∷ A) (Δ ∷ A)
ext ρ v₀ = v₀
ext ρ (vs x) = vs (ρ x)

sw : ∀{Γ A B} → Ren (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
sw v₀ = vs v₀
sw (vs v₀) = v₀
sw (vs (vs x)) = vs (vs x)

cr : ∀{Γ A} → Ren (Γ ∷ A ∷ A) (Γ ∷ A)
cr v₀ = v₀
cr (vs v₀) = v₀
cr (vs (vs x)) = vs x

wk : ∀{Γ Δ A} → Ren Γ Δ → Ren Γ (Δ ∷ A)
wk ρ x = vs (ρ x)

-- Joining context
_++_ : Con → Con → Con
Γ ++ · = Γ
Γ ++ (Δ ∷ A) = (Γ ++ Δ) ∷ A

len-C : Con → ℕ
len-C · = zero
len-C (Γ ∷ _) = suc (len-C Γ)
