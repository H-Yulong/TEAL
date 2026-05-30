module Defunctionalized.Calculus.Syntax where

open import Basic
open import Context

data LCon : Set
data Tm (D : LCon) : Con → Ty → Set
data LVar : (D : LCon) → (Δ : Con) → (A B : Ty) → Set
data St (D : LCon) : Con → Con → Set

data LCon where
  ● : LCon
  _⨾_ : ∀{Δ A B} → (D : LCon) → Tm D (Δ ∷ A) B → LCon

data LVar where
  ℓ₀ : ∀{D Δ A B}{t : Tm D (Δ ∷ A) B} → LVar (D ⨾ t) Δ A B
  ℓs : ∀{D Δ A B}{Δ' A' B'}{t : Tm D (Δ' ∷ A') B'} → LVar D Δ A B → LVar (D ⨾ t) Δ A B

data Tm D where
  var : ∀{Γ A} → (x : Var Γ A) → Tm D Γ A
  lab : ∀{Γ Δ A B} → (ℓ : LVar D Δ A B) → (st : St D Γ Δ) → Tm D Γ (A ⇒ B)
  app : ∀{Γ A B} → (t : Tm D Γ (A ⇒ B)) → (t' : Tm D Γ A) → Tm D Γ B
  unit : ∀{Γ} → Tm D Γ One

data St D where
  ε : ∀{Γ} → St D Γ ·
  _,_ : ∀{Γ Δ A} → St D Γ Δ → Tm D Γ A → St D Γ (Δ ∷ A)

{- Renamings -}
ren : ∀{D Γ Δ A} → Ren Γ Δ → Tm D Γ A → Tm D Δ A
ren-st : ∀{D Γ Δ Δ'} → Ren Γ Δ → St D Γ Δ' → St D Δ Δ'

ren ρ (var x) = var (ρ x)
ren ρ (lab ℓ st) = lab ℓ (ren-st ρ st)
ren ρ (app t t') = app (ren ρ t) (ren ρ t')
ren ρ unit = unit

ren-st ρ ε = ε
ren-st ρ (st , t) = ren-st ρ st , ren ρ t

{- LCon renamings -}
LRen : LCon → LCon → Set
LRen D D' = ∀{Γ A B} → LVar D Γ A B → LVar D' Γ A B

Lren : ∀{D D' Γ A} → LRen D D' → Tm D Γ A → Tm D' Γ A
Lren-st : ∀{D D' Γ Δ} → LRen D D' → St D Γ Δ → St D' Γ Δ

Lren χ (var x) = var x
Lren χ (lab ℓ st) = lab (χ ℓ) (Lren-st χ st)
Lren χ (app t t') = app (Lren χ t) (Lren χ t')
Lren χ unit = unit

Lren-st χ ε = ε
Lren-st χ (st , t) = (Lren-st χ st) , Lren χ t

Lwk : ∀{D Δ A B}{t : Tm D (Δ ∷ A) B} → LRen D (D ⨾ t)
Lwk ℓ₀ = ℓs ℓ₀
Lwk (ℓs ℓ) = ℓs (Lwk ℓ)

{- Substitution -}
_[_] : ∀{D Γ Δ A} → Tm D Δ A → St D Γ Δ → Tm D Γ A
_[_]s : ∀{D Γ Δ Δ'} → St D Δ Δ' → St D Γ Δ → St D Γ Δ'

var v₀ [ σ , t ] = t
var (vs x) [ σ , t ] = (var x) [ σ ]
lab ℓ st [ σ ] = lab ℓ (st [ σ ]s)
app t t' [ σ ] = app (t [ σ ]) (t' [ σ ])
unit [ σ ] = unit

ε [ σ ]s = ε
(st , t) [ σ ]s = (st [ σ ]s) , (t [ σ ])

get : ∀{D Δ A B} → LVar D Δ A B → Tm D (Δ ∷ A) B
get {D = D ⨾ t} ℓ₀ = Lren Lwk t
get {D = D} (ℓs ℓ) = Lren Lwk (get ℓ)



