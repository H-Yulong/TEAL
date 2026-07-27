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
infixl 20 _⋈i_

private variable
  @0 Γ Γ' Γ'' Δ Δ' Δ'' : Con
  @0 A A' B B' C C' A₀ : Ty

mutual
  data Instr : (@0 Γ : Con) → {@0 Δ Δ' : Con} → @0 Stack Γ Δ → @0 Stack Γ Δ' → Set where
    pop : 
      {@0 σ : Stack Γ Δ}{@0 t : Tm Γ A} →
      Instr Γ (σ ∷ t) σ
    swap : 
      {@0 σ : Stack Γ Δ}{@0 t : Tm Γ A}{@0 t' : Tm Γ B} →
      Instr Γ (σ ∷ t ∷ t') (σ ∷ t' ∷ t)
    app : 
      {@0 σ : Stack Γ Δ}{@0 t : Tm Γ (A ⇒ B)}{@0 t' : Tm Γ A} → 
      Instr Γ (σ ∷ t ∷ t') (σ ∷ (M.app t t'))
    unit : 
      {@0 σ : Stack Γ Δ} → 
      Instr Γ σ (σ ∷ M.unit)
    var : 
      {@0 σ : Stack Γ Δ} →
      (x : Var Γ A) → 
      Instr Γ σ (σ ∷ (M.var x))
    st : 
      {@0 σ : Stack Γ Δ} → 
      (x : Var Δ A) → 
      Instr Γ σ (σ ∷ (find-st x σ))
    pushc : 
      {@0 σ : Stack Γ Δ}{@0 σ' : Stack (Γ ∷ A) Δ'}{@0 t : Tm (Γ ∷ A) B} → 
      Is (Γ ∷ A) · (σ' ∷ t) → 
      Instr Γ σ (σ ∷ M.lam t)
    clo : ∀{@0 Δ₁ Δ₂ Δ'} →
      {@0 σ : Stack Γ Δ}{@0 σ₁ : Stack Γ Δ₁}{@0 σ₂ : Stack Γ Δ₂}{@0 σ' : Stack (Δ₂ ∷ A) Δ'}
      {@0 t : Tm (Δ₂ ∷ A) B} → 
      (n : ℕ) →
      ⦃ @0 eq : Δ ≡ (Δ₁ ++ Δ₂) ⦄ → 
      @0 σ ≡ subst (λ z → Stack Γ z) (sym eq) (σ₁ ++s σ₂) → 
      @0 len-C Δ₂ ≡ n → 
      Is (Δ₂ ∷ A) · (σ' ∷ t) → 
      Instr Γ σ (σ₁ ∷ M.lam (t [ ↑ (to-sub σ₂) ]))
    lit : 
      {@0 σ : Stack Γ Δ} → 
      (n : ℕ) → 
      Instr Γ σ (σ ∷ M.lit n)
    suc : 
      {@0 σ : Stack Γ Δ}{@0 t : Tm Γ Nat} → 
      Instr Γ (σ ∷ t) (σ ∷ M.suc t)
    rec : 
      {@0 σ : Stack Γ Δ}{@0 tZ : Tm Γ A}
      {@0 σ' : Stack (Γ ∷ Nat ∷ A) Δ'}{@0 tS : Tm (Γ ∷ Nat ∷ A) A}
      {@0 σ'' : Stack Γ Δ''}{@0 n : Tm Γ Nat} → 
      Is Γ · (σ ∷ tZ) → 
      Is (Γ ∷ Nat ∷ A) · (σ' ∷ tS) → 
      Instr Γ (σ'' ∷ n) (σ'' ∷ M.rec tZ tS n)
    add : 
      {@0 σ : Stack Γ Δ}{@0 t t' : Tm Γ Nat} → 
      Instr Γ (σ ∷ t ∷ t') (σ ∷ M.add t t')
    mult :
      {@0 σ : Stack Γ Δ}{@0 t t' : Tm Γ Nat} → 
      Instr Γ (σ ∷ t ∷ t') (σ ∷ M.mult t t')
    pair : 
      {@0 σ : Stack Γ Δ}{@0 t : Tm Γ A}{@0 t' : Tm Γ B} → 
      Instr Γ (σ ∷ t ∷ t') (σ ∷ M.pair t t')
    fst : 
      {@0 σ : Stack Γ Δ}{@0 t : Tm Γ (A ⊗ B)} → 
     Instr Γ (σ ∷ t) (σ ∷ M.fst t)
    snd : 
      {@0 σ : Stack Γ Δ}{@0 t : Tm Γ (A ⊗ B)} → 
      Instr Γ (σ ∷ t) (σ ∷ M.snd t)

  data Is (@0 Γ : Con) : {@0 Δ : Con} → @0 Stack Γ Δ → @0 Stack Γ Δ' → Set where
    ret : 
      {@0 σ : Stack Γ Δ}{@0 t : Tm Γ A}{@0 t' : Tm Γ A} → 
      @0 ⦃ t ≡ t' ⦄ → 
      Is Γ (σ ∷ t) (σ ∷ t')
    _⨾_ : 
      ∀ {@0 σ : Stack Γ Δ}{@0 σ' : Stack Γ Δ'}{@0 σ'' : Stack Γ Δ''} →  
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
transform-i add = I.add
transform-i mult = I.mult
transform-i pair = I.pair
transform-i fst = I.fst
transform-i snd = I.snd

transform ret = I.ret
transform (i ⨾ ins) = (transform-i i) I.⨾ (transform ins)

exec : {@0 σ : Stack · Δ}{@0 t : Tm · A} → (ins : Is · · (σ ∷ t)) → I.Val A
exec ins = I.interp I.⟨ transform ins , I.· , I.· , I.· ⟩

_⋈i_ : 
  {@0 σ : Stack Γ Δ}{@0 σ' : Stack Γ Δ'}{@0 σ'' : Stack Γ Δ''} →  
  Is Γ σ σ' → Is Γ σ' σ'' → Is Γ σ σ''
(ret ⦃ refl ⦄) ⋈i ins' = ins'
(i ⨾ ins) ⋈i ins' = i ⨾ (ins ⋈i ins')

compile : ∀{@0 σ : Stack Γ Δ} → (t : Source.Tm Γ A) → Is Γ σ (σ ∷ M.compile t)
compile Source.unit = unit ⨾ ret
compile (Source.var x) = var x ⨾ ret
compile (Source.lam t) = pushc (compile t) ⨾ ret
compile (Source.app t t') = (compile t) ⋈i (compile t') ⋈i (app ⨾ ret)
compile (Source.lit n) = lit n ⨾ ret
compile (Source.suc t) = compile t ⋈i (suc ⨾ ret)
compile (Source.add t t') = (compile t) ⋈i (compile t') ⋈i (add ⨾ ret)
compile (Source.mult t t') = (compile t) ⋈i (compile t') ⋈i (mult ⨾ ret)
compile (Source.rec tZ tS t) = (compile t) ⋈i (rec (compile tZ) (compile tS) ⨾ ret)
compile (Source.pair t t') = (compile t) ⋈i (compile t') ⋈i (pair ⨾ ret)
compile (Source.fst t) = (compile t) ⋈i (fst ⨾ ret)
compile (Source.snd t) = (compile t) ⋈i (snd ⨾ ret)

open import IO
open import Agda.Primitive
import Data.Unit.Polymorphic.Base as Base

show-exe : {@0 σ : Stack · Δ}{@0 t : Tm · A} → (ins : Is · · (σ ∷ t)) → IO {lzero} (Base.⊤)
show-exe ins = I.show-exe I.⟨ transform ins , I.· , I.· , I.· ⟩

