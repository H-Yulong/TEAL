module Functional.Calculus.Shallow where

open import Data.Nat hiding (suc)
open import Data.Product renaming (proj₁ to π₁; proj₂ to π₂)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Basic
open import Context
import Functional.Calculus.Syntax as S

{- Shallow embedding of the source calculus -}

⟦_⟧T : Ty → Set
⟦ One ⟧T = ⊤
⟦ Nat ⟧T = ℕ
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T
⟦ A ⊗ B ⟧T = ⟦ A ⟧T × ⟦ B ⟧T

⟦_⟧Γ : Con → Set
⟦ · ⟧Γ = ⊤
⟦ Γ ∷ A ⟧Γ = ⟦ Γ ⟧Γ × ⟦ A ⟧T

{- 
  Custom encoding of functions and pairs, 
  so that the shallow embedding could infer more 
  implicit variables.

  Before:
    Tm Γ A = ⟦ Γ ⟧ → ⟦ A ⟧
    ==> Γ , A are consumed in ⟦_⟧, so can't imply them in most cases
  
  After:
    Tm Γ A = ~Π Γ A
    ==> Γ , A are kept intact, access the underlying function 
        via pattern matching
-}
record ~Π (Γ : Con) (A : Ty) : Set where
  constructor ~λ
  field
    ~fun : ⟦ Γ ⟧Γ → ⟦ A ⟧T
open ~Π

Tm : Con → Ty → Set
Tm Γ A = ~Π Γ A

unit : ∀{Γ} → Tm Γ One
unit = ~λ (λ γ → tt)

var : ∀{Γ A} → Var Γ A → Tm Γ A
var v₀ = ~λ π₂
var (vs x) = ~λ (~Π.~fun (var x) ∘ π₁)

lam : ∀{Γ A B} → Tm (Γ ∷ A) B → Tm Γ (A ⇒ B)
lam (~λ t) = ~λ (λ γ a → t (γ , a))

app : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
app (~λ t) (~λ a) = ~λ (λ γ → t γ (a γ))

lit : ∀{Γ} → (n : ℕ) → Tm Γ Nat
lit n = ~λ (λ γ → n)

suc : ∀{Γ} → Tm Γ Nat → Tm Γ Nat
suc (~λ t) = ~λ (λ γ → ℕ.suc (t γ))

add : ∀{Γ} → Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
add (~λ t) (~λ t') = ~λ (λ γ → (t γ) + (t' γ))

mult : ∀{Γ} → Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
mult (~λ t) (~λ t') = ~λ (λ γ → (t γ) * (t' γ))

~rec : ∀{A : Set} → A → (ℕ → A → A) → ℕ → A
~rec Z S zero = Z
~rec Z S (ℕ.suc n) = S n (~rec Z S n)

rec : ∀{Γ A} → Tm Γ A → Tm (Γ ∷ Nat ∷ A) A → Tm Γ Nat → Tm Γ A
rec (~λ tZ) (~λ tS) (~λ t) = ~λ (λ γ → ~rec (tZ γ) (λ x r → tS ((γ , x) , r)) (t γ))

pair : ∀{Γ A B} → Tm Γ A → Tm Γ B → Tm Γ (A ⊗ B)
pair (~λ t) (~λ t') = ~λ (λ γ → t γ , t' γ)

fst : ∀{Γ A B} → Tm Γ (A ⊗ B) → Tm Γ A
fst (~λ t) = ~λ (λ γ → π₁ (t γ))

snd : ∀{Γ A B} → Tm Γ (A ⊗ B) → Tm Γ B
snd (~λ t) = ~λ (λ γ → π₂ (t γ))

proj₁ : 
  ∀{Γ A B}{t : Tm Γ (A ⊗ B)}{t₁ : Tm Γ A}{t₂ : Tm Γ B} → 
  pair t₁ t₂ ≡ t → t₁ ≡ fst t
proj₁ refl = refl

proj₂ : 
  ∀{Γ A B}{t : Tm Γ (A ⊗ B)}{t₁ : Tm Γ A}{t₂ : Tm Γ B} → 
  pair t₁ t₂ ≡ t → t₂ ≡ snd t
proj₂ refl = refl

Sub : Con → Con → Set
Sub Γ Δ = ⟦ Γ ⟧Γ → ⟦ Δ ⟧Γ

✧ : ∀{Γ} → Sub Γ Γ
✧ γ = γ

_[_] : ∀{Γ Δ A} → Tm Δ A → Sub Γ Δ → Tm Γ A
(~λ t) [ σ ] = ~λ (λ γ → t (σ γ))

_▻_ : ∀{Γ Δ A} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ∷ A)
σ ▻ (~λ t) = λ γ → (σ γ) , (t γ)

p : ∀{Γ A} → Sub (Γ ∷ A) Γ
p = π₁

q : ∀{Γ A} → Tm (Γ ∷ A) A
q = ~λ π₂

⊘ : ∀{Γ} → Sub Γ ·
⊘ γ = tt

↑ : ∀{Γ Δ A} → Sub Γ Δ → Sub (Γ ∷ A) (Δ ∷ A)
↑ σ (γ , a) = σ γ , a

rec-Z : ∀{Γ A}{n : Tm Γ Nat}{tZ : Tm Γ A}{tS : Tm (Γ ∷ Nat ∷ A) A} → n ≡ (lit zero) → tZ ≡ rec tZ tS n
rec-Z refl = refl

rec-S : ∀{Γ A}{m n : Tm Γ Nat}{tZ : Tm Γ A}{tS : Tm (Γ ∷ Nat ∷ A) A} → m ≡ suc n → tS [ (✧ ▻ n) ▻ rec tZ tS n ] ≡ rec tZ tS m
rec-S refl = refl

compile : ∀{Γ A} → S.Tm Γ A → Tm Γ A
compile S.unit = unit
compile (S.var x) = var x
compile (S.lam t) = lam (compile t)
compile (S.app t t') = app (compile t) (compile t')
compile (S.lit n) = lit n
compile (S.suc t) = suc (compile t)
compile (S.add t t') = add (compile t) (compile t')
compile (S.mult t t') = mult (compile t) (compile t')
compile (S.rec tZ tS t) = rec (compile tZ) (compile tS) (compile t)
compile (S.pair t t') = pair (compile t) (compile t')
compile (S.fst t) = fst (compile t)
compile (S.snd t) = snd (compile t)
