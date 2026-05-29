module Functional.Calculus.Syntax where

open import Basic
open import Context

open import Data.Nat

infix 20 _[_]
infix 5 _≡β_
infixl 30 _▻_

data Tm : Con → Ty → Set where
  unit : ∀{Γ} → Tm Γ One
  var : ∀{Γ A} → Var Γ A → Tm Γ A
  lam : ∀{Γ A B} → Tm (Γ ∷ A) B → Tm Γ (A ⇒ B)
  app : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  lit : ∀{Γ} → (n : ℕ) → Tm Γ Nat
  suc : ∀{Γ} → Tm Γ Nat → Tm Γ Nat
  add mult : ∀{Γ} → Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
  rec : ∀{Γ A} → Tm Γ A → Tm (Γ ∷ Nat ∷ A) A → Tm Γ Nat → Tm Γ A

{- Renaming and substitution -}
ren : ∀{Γ Δ A} → Tm Γ A → Ren Γ Δ → Tm Δ A
ren unit ρ = unit
ren (var x) ρ = var (ρ x)
ren (lam t) ρ = lam (ren t (ext ρ))
ren (app t t') ρ = app (ren t ρ) (ren t' ρ) 
ren (lit n) ρ = lit n
ren (suc t) ρ = suc (ren t ρ)
ren (add t t') ρ = add (ren t ρ) (ren t' ρ)
ren (mult t t') ρ = mult (ren t ρ) (ren t' ρ)
ren (rec tZ tS t) ρ = rec (ren tZ ρ) (ren tS (ext (ext ρ))) (ren t ρ)

Sub : Con → Con → Set
Sub Γ Δ = ∀{A} → Var Δ A → Tm Γ A

↑ : ∀{Γ Δ A} → Sub Γ Δ → Sub (Γ ∷ A) (Δ ∷ A)
↑ σ v₀ = var v₀
↑ σ (vs x) = ren (σ x) vs

_[_] : ∀{Γ Δ A} → Tm Δ A → Sub Γ Δ → Tm Γ A
unit [ σ ] = unit
var x [ σ ] = σ x
lam t [ σ ] = lam (t [ ↑ σ ])
app t t' [ σ ] = app (t [ σ ]) (t' [ σ ])
lit n [ σ ] = lit n
suc t [ σ ] = suc (t [ σ ])
add t t' [ σ ] = add (t [ σ ]) (t' [ σ ])
mult t t' [ σ ] = mult (t [ σ ]) (t' [ σ ])
rec tZ tS t [ σ ] = rec (tZ [ σ ]) (tS [ ↑ (↑ σ) ]) (t [ σ ])

✧ : ∀{Γ} → Sub Γ Γ
✧ x = var x

⊘ : ∀{Γ} → Sub Γ ·
⊘ ()

_▻_ : ∀{Γ Δ A} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ∷ A)
(σ ▻ t) v₀ = t
(σ ▻ t) (vs x) = σ x

_~_ : ∀{Γ Δ Δ'} → Sub Γ Δ → Sub Δ' Γ → Sub Δ' Δ
(σ ~ σ') x = (σ x) [ σ' ]

data _≡β_ : {Γ : Con} {A : Ty} → (t t' : Tm Γ A) → Set where
  β : 
    ∀{Γ A B}{t : Tm (Γ ∷ A) B}{t' : Tm Γ A} → 
    app (lam t) t' ≡β t [ ✧ ▻ t' ] 
  η : 
    ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → 
    lam (app (ren t vs) (var v₀)) ≡β t
  -- natural numbers
  addZ : ∀{Γ}{t : Tm Γ Nat} → add (lit zero) t ≡β t
  addS : ∀{Γ}{t t' : Tm Γ Nat} → add (suc t) t' ≡β suc (add t t')
  multZ : ∀{Γ}{t : Tm Γ Nat} → mult (lit zero) t ≡β lit zero
  multS : ∀{Γ}{t t' : Tm Γ Nat} → mult (suc t) t' ≡β add t' (mult t t')
  recZ : ∀{Γ A}{tZ : Tm Γ A}{tS : Tm (Γ ∷ Nat ∷ A) A} → rec tZ tS (lit zero) ≡β tZ
  recS : 
    ∀{Γ A}{tZ : Tm Γ A}{tS : Tm (Γ ∷ Nat ∷ A) A}{t : Tm Γ Nat} → 
    rec tZ tS (suc t) ≡β tS [ ✧ ▻ t ▻ rec tZ tS t ]
  suc : ∀{Γ n} → _≡β_ {Γ} (suc (lit n)) (lit (suc n))
  -- congruence rules
  cong-lam : 
    ∀{Γ A B}{t t' : Tm (Γ ∷ A) B} → 
    t ≡β t' → lam t ≡β lam t'
  cong-app : 
    ∀{Γ A B}{s s' : Tm Γ (A ⇒ B)}{t t' : Tm Γ A} → 
    s ≡β s' → t ≡β t' → app s t ≡β app s' t'
  cong-add : 
    ∀{Γ}{s s' t t' : Tm Γ Nat} → 
    s ≡β s' → t ≡β t' → add s t ≡β add s' t'
  cong-mult : 
    ∀{Γ}{s s' t t' : Tm Γ Nat} → 
    s ≡β s' → t ≡β t' → mult s t ≡β mult s' t'
  cong-suc : 
    ∀{Γ}{t t' : Tm Γ Nat} → 
    t ≡β t' → suc t ≡β suc t'
  cong-rec : 
    ∀{Γ A}{tZ tZ' : Tm Γ A}{tS tS' : Tm (Γ ∷ Nat ∷ A) A}{t t' : Tm Γ Nat} →
    tZ ≡β tZ' → tS ≡β tS' → t ≡β t' → 
    rec tZ tS t ≡β rec tZ' tS' t'

