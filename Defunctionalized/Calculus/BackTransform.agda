module Defunctionalized.Calculus.BackTransform where

open import Relation.Binary.PropositionalEquality 

open import Basic
open import Context
open import Defunctionalized.Calculus.Syntax

import Functional.Calculus.Syntax as S
-- open import STLC.Properties

{- Backward transformation -}

⟦_⟧ : ∀{D Γ A} → Tm D Γ A → S.Tm Γ A
⟦_⟧ℓ : ∀{D Δ A B} → LVar D Δ A B → S.Tm (Δ ∷ A) B
⟦_⟧s : ∀{D Γ Δ} → St D Γ Δ → S.Sub Γ Δ

⟦ var x ⟧ = S.var x
⟦ lab ℓ st ⟧ = (S.lam ⟦ ℓ ⟧ℓ) S.[ ⟦ st ⟧s ]
⟦ app t t' ⟧ = S.app ⟦ t ⟧ ⟦ t' ⟧
⟦ unit ⟧ = S.unit

⟦_⟧ℓ {D = D ⨾ t} ℓ₀ = ⟦ t ⟧
⟦_⟧ℓ {D = D ⨾ t} (ℓs ℓ) = ⟦ ℓ ⟧ℓ

⟦ ε ⟧s = λ ()
⟦ st , t ⟧s = ⟦ st ⟧s S.▻ ⟦ t ⟧

{-
{- Correctness proofs : later. -} 
Lem-subst : ∀{D Γ Δ A} → (t : Tm D Γ A) → (σ : St D Δ Γ) → ⟦ t [ σ ] ⟧ ≡ ⟦ t ⟧ S.[ ⟦ σ ⟧s ]
Lem-subst-st : ∀{D Γ Δ Δ'} → (st : St D Γ Δ) → (σ : St D Δ' Γ) → ⟦ st [ σ ]s ⟧s ~= (⟦ st ⟧s S.~ ⟦ σ ⟧s)

Lem-subst (var v₀) (σ , t) = refl
Lem-subst (var (vs x)) (σ , t) = Lem-subst (var x) σ
Lem-subst (lab ℓ st) σ = cong S.lam {!  !}
Lem-subst (app t t') σ = cong₂ S.app (Lem-subst t σ) (Lem-subst t' σ)
Lem-subst unit σ = refl

Lem-subst-st (st , t) σ v₀ = Lem-subst t σ
Lem-subst-st (st , t) σ (vs x) = Lem-subst-st st σ x

Lem-red-lock : ∀{D Γ A}{s t : Tm D Γ A} → s ⟶ t → ⟦ s ⟧ S.⟶ ⟦ t ⟧
Lem-red-lock {D ⨾ t'} (red-β {ℓ = ℓ₀} {st} {t}) = 
  let P = (λ x → (S.app (S.lam (⟦ t' ⟧ S.[ S.↑ ⟦ st ⟧s ])) ⟦ t ⟧) S.⟶ x) 
  in
    subst P {!   !} S.red-β
Lem-red-lock (red-β {ℓ = ℓs ℓ}) = {!   !}
Lem-red-lock (red-app move) = S.red-app (Lem-red-lock move)
-}



