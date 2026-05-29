module Functional.TermMachine.Intrinsic where

open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Basic
open import Context

import Functional.Syntax as S
import Functional.Calculus.Shallow as M
import Functional.TermMachine.Types as T
import Functional.TypeMachine.Termination as H
import Functional.Calculus.Syntax as Source

open M using (Tm; Sub; _[_]; ↑; _▻_; ~λ; ✧; ⊘)
open M.~Π
open T using (Stack; ·; _∷_; find-st; _++s_; to-sub)

infixr 20 _⨾_
infixl 20 _⋈_

private variable
  Γ Γ' Γ'' Δ Δ' Δ'' : Con
  A A' B B' C C' A₀ : Ty

mutual
  data Instr : (Γ : Con) → {Δ Δ' : Con} → Stack Γ Δ → Stack Γ Δ' → Set where
    pop : 
      {σ : Stack Γ Δ}{t : Tm Γ A} →
      Instr Γ (σ ∷ t) σ
    swap : 
      {σ : Stack Γ Δ}{t : Tm Γ A}{t' : Tm Γ B} →
      Instr Γ (σ ∷ t ∷ t') (σ ∷ t' ∷ t)
    app : 
      {σ : Stack Γ Δ}{t : Tm Γ (A ⇒ B)}{t' : Tm Γ A} → 
      Instr Γ (σ ∷ t ∷ t') (σ ∷ (M.app t t'))
    unit : 
      {σ : Stack Γ Δ} → 
      Instr Γ σ (σ ∷ M.unit)
    var : 
      {σ : Stack Γ Δ} →
      (x : Var Γ A) → 
      Instr Γ σ (σ ∷ (M.var x))
    st : 
      {σ : Stack Γ Δ} → 
      (x : Var Δ A) → 
      Instr Γ σ (σ ∷ (find-st x σ))
    pushc : 
      {σ : Stack Γ Δ}{σ' : Stack (Γ ∷ A) Δ'}{t : Tm (Γ ∷ A) B} → 
      Is (Γ ∷ A) · (σ' ∷ t) → 
      Instr Γ σ (σ ∷ M.lam t)
    clo : ∀{n Δ₁ Δ₂ Δ'} →
      {σ : Stack Γ Δ}{σ₁ : Stack Γ Δ₁}{σ₂ : Stack Γ Δ₂}{σ' : Stack (Δ₂ ∷ A) Δ'}
      {t : Tm (Δ₂ ∷ A) B} → 
      ⦃ eq : Δ ≡ (Δ₁ ++ Δ₂) ⦄ → 
      σ ≡ subst (λ z → Stack Γ z) (sym eq) (σ₁ ++s σ₂) → 
      len-C Δ₂ ≡ n → 
      Is (Δ₂ ∷ A) · (σ' ∷ t) → 
      Instr Γ σ (σ₁ ∷ M.lam (t [ ↑ (to-sub σ₂) ]))
    lit : 
      {σ : Stack Γ Δ} → 
      (n : ℕ) → 
      Instr Γ σ (σ ∷ M.lit n)
    suc : 
      {σ : Stack Γ Δ}{t : Tm Γ Nat} → 
      Instr Γ (σ ∷ t) (σ ∷ M.suc t)
    rec : 
      {σ : Stack Γ Δ}{tZ : Tm Γ A}
      {σ' : Stack (Γ ∷ Nat ∷ A) Δ'}{tS : Tm (Γ ∷ Nat ∷ A) A}
      {σ'' : Stack Γ Δ''}{n : Tm Γ Nat} → 
      Is Γ · (σ ∷ tZ) → 
      Is (Γ ∷ Nat ∷ A) · (σ' ∷ tS) → 
      Instr Γ (σ'' ∷ n) (σ'' ∷ M.rec tZ tS n)
    add : 
      {σ : Stack Γ Δ}{t t' : Tm Γ Nat} → 
      Instr Γ (σ ∷ t ∷ t') (σ ∷ M.add t t')
    mult :
      {σ : Stack Γ Δ}{t t' : Tm Γ Nat} → 
      Instr Γ (σ ∷ t ∷ t') (σ ∷ M.mult t t')

  data Is (Γ : Con) : {Δ : Con} → Stack Γ Δ → Stack Γ Δ' → Set where
    ret : 
      {σ : Stack Γ Δ}{t : Tm Γ A}{t' : Tm Γ A} → 
      ⦃ t ≡ t' ⦄ → 
      Is Γ (σ ∷ t) (σ ∷ t')
    _⨾_ : 
      ∀ {σ : Stack Γ Δ}{σ' : Stack Γ Δ'}{σ'' : Stack Γ Δ''} →  
      Instr Γ σ σ' → Is Γ σ' σ'' → 
      Is Γ σ σ''

mutual
  transform-i : 
    {σ : Stack Γ Δ}{σ' : Stack Γ Δ'} → 
    Instr Γ σ σ' → Σ S.Instr (λ ins → Γ T.⊢ᵢ ins ∈ σ ⟶ σ')
  transform-i pop = S.pop , T.Ty-pop
  transform-i swap = S.swap , T.Ty-swap
  transform-i app = S.app , T.Ty-app
  transform-i unit = S.unit , T.Ty-unit
  transform-i (var x) = S.var x , T.Ty-var x
  transform-i (st x) = S.st x , T.Ty-st x
  transform-i (pushc ins) = 
    let ins , ty-ins = transform ins in
    S.pushc ins , T.Ty-pushc ty-ins
  transform-i (clo {n = n} eq-s eq-n ins) = 
    let ins , ty-ins = transform ins in
    S.clo n ins , T.Ty-clo eq-s eq-n ty-ins
  transform-i (lit n) = S.lit n , T.Ty-lit n
  transform-i suc = S.suc , T.Ty-suc
  transform-i (rec iZ iS) = 
    let iZ , tZ = transform iZ in
    let iS , tS = transform iS in
    S.rec iZ iS , T.Ty-rec tZ tS
  transform-i add = S.add , T.Ty-add
  transform-i mult = S.mult , T.Ty-mult

  transform : 
    {σ : Stack Γ Δ}{σ' : Stack Γ Δ'} → 
    Is Γ σ σ' → Σ S.Is (λ ins → Γ T.⊢ ins ∈ σ ⟶ σ')
  transform ret = S.ret , T.Ty-ret
  transform (i ⨾ ins) = 
    let i , ty-i = transform-i i in
    let ins , ty-ins = transform ins in
    i S.⨾ ins , T.Ty-⨾ ty-i ty-ins

Exec : {σ : Stack · Δ}{t : Tm · A} → Is · · (σ ∷ t) → Set
Exec ins = Σ S.Val (λ v → S.⟨ (π₁ (transform ins)) , S.· , S.· , S.· ⟩ S.⇓ v)

exec : {σ : Stack · Δ}{t : Tm · A} → (ins : Is · · (σ ∷ t)) → Exec ins
exec ins = 
  let v , σ , _ = T.Total-Correctness-Prog (π₂ (transform ins)) in
    v , σ

_⋈_ : 
  {σ : Stack Γ Δ}{σ' : Stack Γ Δ'}{σ'' : Stack Γ Δ''} →  
  Is Γ σ σ' → Is Γ σ' σ'' → Is Γ σ σ''
(ret ⦃ refl ⦄) ⋈ ins' = ins'
(i ⨾ ins) ⋈ ins' = i ⨾ (ins ⋈ ins')

compile : (t : Source.Tm Γ A) → Is Γ · (· ∷ (M.compile t))
compile t = aux t
  where
    aux : {σ : Stack Γ Δ} → (t : Source.Tm Γ A) → Is Γ σ (σ ∷ (M.compile t))
    aux Source.unit = unit ⨾ ret
    aux (Source.var x) = var x ⨾ ret
    aux (Source.lam t) = pushc (aux t) ⨾ ret
    aux (Source.app t t') = (aux t) ⋈ (aux t') ⋈ (app ⨾ ret)
    aux (Source.lit n) = lit n ⨾ ret
    aux (Source.suc t) = aux t ⋈ (suc ⨾ ret)
    aux (Source.add t t') = (aux t) ⋈ (aux t') ⋈ (add ⨾ ret)
    aux (Source.mult t t') = (aux t) ⋈ (aux t') ⋈ (mult ⨾ ret)
    aux (Source.rec tZ tS t) = (aux t) ⋈ (rec (aux tZ) (aux tS) ⨾ ret)


