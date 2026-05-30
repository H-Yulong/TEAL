module Functional.TypeMachine.Intrinsic where

open import Basic
open import Context
open import Functional.Calculus.Syntax
open import Functional.TypeMachine.Types

import Functional.Syntax as S
import Functional.TypeMachine.Termination as T

open import Data.Nat
open import Data.Product renaming (proj₁ to π₁; proj₂ to π₂) hiding (swap)

private variable
  Γ Γ' Γ'' Δ Δ' Δ'' : Con
  A A' B B' C C' A₀ : Ty

infixr 20 _⨾_
infixl 20 _⋈_

data Instr : Con → Con → Con → Set
data Is : Con → Con → Con → Set

data Instr where
  pop : Instr Γ (Δ ∷ A) Δ
  swap : Instr Γ (Δ ∷ A ∷ B) (Δ ∷ B ∷ A)
  app : Instr Γ (Δ ∷ (A ⇒ B) ∷ A) (Δ ∷ B)
  unit : Instr Γ Δ (Δ ∷ One)
  var : (x : Var Γ A) → Instr Γ Δ (Δ ∷ A)
  st :(x : Var Δ A) → Instr Γ Δ (Δ ∷ A)
  pushc : Is (Γ ∷ A) · (Δ' ∷ B) → Instr Γ Δ (Δ ∷ A ⇒ B)
  lit : (n : ℕ) → Instr Γ Δ (Δ ∷ Nat)
  suc : Instr Γ (Δ ∷ Nat) (Δ ∷ Nat)
  rec : 
    Is Γ · (Δ ∷ A) → 
    Is (Γ ∷ Nat ∷ A) · (Δ' ∷ A) → 
    Instr Γ (Δ'' ∷ Nat) (Δ'' ∷ A)
  add : Instr Γ (Δ ∷ Nat ∷ Nat) (Δ ∷ Nat)
  mult : Instr Γ (Δ ∷ Nat ∷ Nat) (Δ ∷ Nat)
  pair : Instr Γ (Δ ∷ A ∷ B) (Δ ∷ A ⊗ B)
  fst : Instr Γ (Δ ∷ A ⊗ B) (Δ ∷ A)
  snd : Instr Γ (Δ ∷ A ⊗ B) (Δ ∷ B)

data Is where
  ret : Is Γ (Δ ∷ A) (Δ ∷ A)
  _⨾_ : Instr Γ Δ Δ' → Is Γ Δ' Δ'' → Is Γ Δ Δ''


transform-i : Instr Γ Δ Δ' → (Σ S.Instr (λ ins → Γ ⊢ᵢ ins ∈ Δ ⟶ Δ'))
transform : Is Γ Δ Δ' → (Σ S.Is (λ ins → Γ ⊢ ins ∈ Δ ⟶ Δ'))

transform-i pop = S.pop , Ty-pop
transform-i swap = S.swap , Ty-swap
transform-i app = S.app , Ty-app
transform-i unit = S.unit , Ty-unit
transform-i (var x) = S.var x , Ty-var x
transform-i (st x) = S.st x , Ty-st x
transform-i (pushc ins) with transform ins
... | ins , ty-ins = S.pushc ins , Ty-pushc ty-ins
transform-i (lit n) = S.lit n , Ty-lit n
transform-i suc = S.suc , Ty-suc
transform-i (rec inZ inS) with transform inZ | transform inS
... | inZ , tyZ | inS , tyS = S.rec inZ inS , Ty-rec tyZ tyS
transform-i add = S.add , Ty-add
transform-i mult = S.mult , Ty-mult
transform-i pair = S.pair , Ty-pair
transform-i fst = S.fst , Ty-fst
transform-i snd = S.snd , Ty-snd


transform ret = S.ret , Ty-ret
transform (i ⨾ ins) with transform-i i | transform ins
... | i , ti | ins , ty-ins = i S.⨾ ins , Ty-⨾ ti ty-ins

Exec : Is · · (Δ ∷ A) → Set
Exec ins = Σ S.Val (λ v → S.⟨ (π₁ (transform ins)) , S.· , S.· , S.· ⟩ S.⇓ v)

exec : (ins : Is · · (Δ ∷ A)) → Exec ins
exec ins = T.exec (π₂ (transform ins))

_⋈_ : Is Γ Δ Δ' → Is Γ Δ' Δ'' → Is Γ Δ Δ''
ret ⋈ ins' = ins'
(i ⨾ ins) ⋈ ins' = i ⨾ (ins ⋈ ins')

compile : Tm Γ A → Is Γ · (· ∷ A)
compile t = aux t
  where
    aux : Tm Γ A → Is Γ Δ (Δ ∷ A)
    aux unit = unit ⨾ ret
    aux (var x) = var x ⨾ ret
    aux (lam t) = pushc (aux t) ⨾ ret
    aux (app t t') = (aux t) ⋈ (aux t') ⋈ (app ⨾ ret)
    aux (lit n) = lit n ⨾ ret
    aux (suc t) = aux t ⋈ (suc ⨾ ret)
    aux (add t t') = (aux t) ⋈ (aux t') ⋈ (add ⨾ ret)
    aux (mult t t') = (aux t) ⋈ (aux t') ⋈ (mult ⨾ ret)
    aux (rec tZ tS t) = (aux t) ⋈ (rec (aux tZ) (aux tS) ⨾ ret)
    aux (pair t t') = (aux t) ⋈ (aux t') ⋈ (pair ⨾ ret)
    aux (fst t) = (aux t) ⋈ (fst ⨾ ret)
    aux (snd t) = (aux t) ⋈ (snd ⨾ ret)
