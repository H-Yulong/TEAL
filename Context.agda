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

data Var : @0 Con → @0 Ty → Set where
  v₀ : ∀{@0 Γ A} → Var (Γ ∷ A) A
  vs : ∀{@0 Γ A B} → Var Γ A → Var (Γ ∷ B) A 

v₁ : ∀{@0 Γ A B} → Var (Γ ∷ A ∷ B) A
v₁ = vs v₀

v₂ : ∀{@0 Γ A B C} → Var (Γ ∷ A ∷ B ∷ C) A
v₂ = vs (vs v₀)

v₃ : ∀{@0 Γ A B C D} → Var (Γ ∷ A ∷ B ∷ C ∷ D) A
v₃ = vs (vs (vs v₀))

{- Renamings -}
@0 Ren : @0 Con → @0 Con → Set
Ren Γ Δ = ∀{@0 A} → Var Γ A → Var Δ A

ext : ∀{@0 Γ Δ A} → Ren Γ Δ → Ren (Γ ∷ A) (Δ ∷ A)
ext ρ v₀ = v₀
ext ρ (vs x) = vs (ρ x)

sw : ∀{@0 Γ A B} → Ren (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
sw v₀ = vs v₀
sw (vs v₀) = v₀
sw (vs (vs x)) = vs (vs x)

cr : ∀{@0 Γ A} → Ren (Γ ∷ A ∷ A) (Γ ∷ A)
cr v₀ = v₀
cr (vs v₀) = v₀
cr (vs (vs x)) = vs x

wk : ∀{@0 Γ Δ A} → Ren Γ Δ → Ren Γ (Δ ∷ A)
wk ρ x = vs (ρ x)

-- Joining context
@0 _++_ : Con → Con → Con
Γ ++ · = Γ
Γ ++ (Δ ∷ A) = (Γ ++ Δ) ∷ A

@0 len-C : Con → ℕ
len-C · = zero
len-C (Γ ∷ _) = suc (len-C Γ)
