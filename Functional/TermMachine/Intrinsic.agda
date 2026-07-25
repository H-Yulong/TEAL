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
import Functional.TypeMachine.Intrinsic as I
import Functional.Calculus.Syntax as Source

open M using (Tm; Sub; _[_]; ↑; _▻_; ~λ; ✧; ⊘)
open M.~Π
open T using (Stack; ·; _∷_; find-st; _++s_; to-sub)

infixr 20 _⨾_
-- infixl 20 _⋈_

private variable
  @0 Γ Γ' Γ'' Δ Δ' Δ'' : Con
  @0 A A' B B' C C' A₀ : Ty

mutual
  data Instr : (@0 Γ : Con) → {@0 Δ Δ' : Con} → @0 Stack Γ Δ → @0 Stack Γ Δ' → Set where
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
    clo : ∀{@0 Δ₁ Δ₂ Δ'} →
      {σ : Stack Γ Δ}{σ₁ : Stack Γ Δ₁}{σ₂ : Stack Γ Δ₂}{σ' : Stack (Δ₂ ∷ A) Δ'}
      {t : Tm (Δ₂ ∷ A) B} → 
      (n : ℕ) →
      ⦃ @0 eq : Δ ≡ (Δ₁ ++ Δ₂) ⦄ → 
      @0 σ ≡ subst (λ z → Stack Γ z) (sym eq) (σ₁ ++s σ₂) → 
      @0 len-C Δ₂ ≡ n → 
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
    pair : 
      {σ : Stack Γ Δ}{t : Tm Γ A}{t' : Tm Γ B} → 
      Instr Γ (σ ∷ t ∷ t') (σ ∷ M.pair t t')
    fst : 
      {σ : Stack Γ Δ}{t : Tm Γ (A ⊗ B)} → 
     Instr Γ (σ ∷ t) (σ ∷ M.fst t)
    snd : 
      {σ : Stack Γ Δ}{t : Tm Γ (A ⊗ B)} → 
      Instr Γ (σ ∷ t) (σ ∷ M.snd t)

  data Is (@0 Γ : Con) : {@0 Δ : Con} → @0 Stack Γ Δ → @0 Stack Γ Δ' → Set where
    ret : 
      {σ : Stack Γ Δ}{t : Tm Γ A}{t' : Tm Γ A} → 
      ⦃ t ≡ t' ⦄ → 
      Is Γ (σ ∷ t) (σ ∷ t')
    _⨾_ : 
      ∀ {σ : Stack Γ Δ}{σ' : Stack Γ Δ'}{σ'' : Stack Γ Δ''} →  
      Instr Γ σ σ' → Is Γ σ' σ'' → 
      Is Γ σ σ''

transform-i : 
  {@0 σ : Stack Γ Δ}{@0 σ' : Stack Γ Δ'} → 
  Instr Γ σ σ' → I.Instr Γ Δ Δ'
transform : 
  {@0 σ : Stack Γ Δ}{@0 σ' : Stack Γ Δ'} →
  Is Γ σ σ' → I.Is Γ Δ Δ'

transform-i pop = I.pop
transform-i swap = I.swap
transform-i app = I.app
transform-i unit = I.unit
transform-i (var x) = I.var x
transform-i (st x) = I.st x
transform-i (pushc ins) = I.pushc (transform ins)
transform-i (clo n ⦃ eq ⦄ eq-s len ins) = I.clo n eq len (transform ins)
transform-i (lit n) = I.lit n
transform-i suc = I.suc
transform-i (rec iZ iS) = I.rec (transform iZ) (transform iS)
transform-i add = I.pop
transform-i mult = I.pop
transform-i pair = I.pair
transform-i fst = I.fst
transform-i snd = I.snd

transform ret = I.ret
transform (i ⨾ ins) = (transform-i i) I.⨾ (transform ins)

interp : {σ : Stack · Δ}{t : Tm · A} → (ins : Is · · (σ ∷ t)) → I.Val A
interp ins = I.interp I.⟨ transform ins , I.· , I.· , I.· ⟩


