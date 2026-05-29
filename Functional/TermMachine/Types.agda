module Functional.TermMachine.Types where

open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.Sum hiding (swap)
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Basic
open import Context
open import Functional.Syntax

import Functional.Calculus.Shallow as M
import Functional.TypeMachine.Types as T
import Functional.TypeMachine.Termination as H

open M using (Tm; Sub; _[_]; ↑; _▻_; ~λ; ✧; ⊘)
open M.~Π

{- 
  Schedule
  3. Refactor, with clearer style:
    - Use let-pattern matching instead of with construct
    - Infix notations for typing environments and stacks
    - Better names for lemmas
    - Organize code with comments
  4. Add examples
  5. Have a look into the DFC style
-}


private variable
  Γ Γ' Γ'' Δ Δ' Δ'' : Con
  A A' B B' C C' A₀ : Ty
  ins ins' ins'' : Is
  v v' v'' : Val
  env env' env'' stack stack' stack'' : Env
  fr fr' : Frame
  c c' c'' c₀ : Config


infix 10 _⊢ᵢ_∈_⟶_
infix 10 _⊢_∈_⟶_

data Stack (Γ : Con) : Con → Set where
  · : Stack Γ ·
  _∷_ : Stack Γ Δ → Tm Γ A → Stack Γ (Δ ∷ A)

find-st : Var Δ A → Stack Γ Δ → Tm Γ A
find-st v₀ (σ ∷ t) = t
find-st (vs v) (σ ∷ t) = find-st v σ

to-sub : Stack Γ Δ → Sub Γ Δ
to-sub · = ⊘
to-sub (σ ∷ t) = to-sub σ ▻ t

_++s_ : Stack Γ Δ → Stack Γ Δ' → Stack Γ (Δ ++ Δ')
σ ++s · = σ
σ ++s (σ' ∷ t) = (σ ++s σ') ∷ t

{- Typing instructions -}
mutual
  data _⊢ᵢ_∈_⟶_ : (Γ : Con) → Instr → Stack Γ Δ → Stack Γ Δ' → Set where
    Ty-pop : 
      {σ : Stack Γ Δ}{t : Tm Γ A} →
      Γ ⊢ᵢ pop ∈ σ ∷ t ⟶ σ
    Ty-swap : 
      {σ : Stack Γ Δ}{t : Tm Γ A}{t' : Tm Γ B} →
      Γ ⊢ᵢ swap ∈ σ ∷ t ∷ t' ⟶ σ ∷ t' ∷ t
    Ty-app : 
      {σ : Stack Γ Δ}{t : Tm Γ (A ⇒ B)}{t' : Tm Γ A} → 
      Γ ⊢ᵢ app ∈ σ ∷ t ∷ t' ⟶ σ ∷ (M.app t t')
    Ty-unit : 
      {σ : Stack Γ Δ} → 
      Γ ⊢ᵢ unit ∈ σ ⟶ σ ∷ M.unit
    Ty-var : 
      {σ : Stack Γ Δ} →
      (x : Var Γ A) → 
      Γ ⊢ᵢ var x ∈ σ ⟶ σ ∷ (M.var x)
    Ty-st : 
      {σ : Stack Γ Δ} → 
      (x : Var Δ A) → 
      Γ ⊢ᵢ st x ∈ σ ⟶ σ ∷ (find-st x σ)
    Ty-pushc : 
      {σ : Stack Γ Δ}{σ' : Stack (Γ ∷ A) Δ'}{t : Tm (Γ ∷ A) B} → 
      (Γ ∷ A) ⊢ ins ∈ · ⟶ σ' ∷ t → 
      Γ ⊢ᵢ pushc ins ∈ σ ⟶ σ ∷ M.lam t
    Ty-clo : ∀{n Δ₁ Δ₂ Δ'} →
      {σ : Stack Γ Δ}{σ₁ : Stack Γ Δ₁}{σ₂ : Stack Γ Δ₂}{σ' : Stack (Δ₂ ∷ A) Δ'}
      {t : Tm (Δ₂ ∷ A) B} → 
      ⦃ eq : Δ ≡ (Δ₁ ++ Δ₂) ⦄ → 
      σ ≡ subst (λ z → Stack Γ z) (sym eq) (σ₁ ++s σ₂) → 
      len-C Δ₂ ≡ n → 
      (Δ₂ ∷ A) ⊢ ins ∈ · ⟶ (σ' ∷ t) → 
      Γ ⊢ᵢ clo n ins ∈ σ ⟶ σ₁ ∷ M.lam (t [ ↑ (to-sub σ₂) ])
    Ty-lit : 
      {σ : Stack Γ Δ} → 
      (n : ℕ) → 
      Γ ⊢ᵢ lit n ∈ σ ⟶ σ ∷ M.lit n
    Ty-suc : 
      {σ : Stack Γ Δ}{t : Tm Γ Nat} → 
      Γ ⊢ᵢ suc ∈ σ ∷ t ⟶ σ ∷ M.suc t
    Ty-rec : 
      {σ : Stack Γ Δ}{tZ : Tm Γ A}
      {σ' : Stack (Γ ∷ Nat ∷ A) Δ'}{tS : Tm (Γ ∷ Nat ∷ A) A}
      {σ'' : Stack Γ Δ''}{n : Tm Γ Nat} → 
      Γ ⊢ ins ∈ · ⟶ σ ∷ tZ → 
      (Γ ∷ Nat ∷ A) ⊢ ins' ∈ · ⟶ σ' ∷ tS → 
      Γ ⊢ᵢ rec ins ins' ∈ σ'' ∷ n ⟶ σ'' ∷ M.rec tZ tS n
    Ty-add : 
      {σ : Stack Γ Δ}{t t' : Tm Γ Nat} → 
      Γ ⊢ᵢ add ∈ σ ∷ t ∷ t' ⟶ σ ∷ M.add t t'
    Ty-mult :
      {σ : Stack Γ Δ}{t t' : Tm Γ Nat} → 
      Γ ⊢ᵢ mult ∈ σ ∷ t ∷ t' ⟶ σ ∷ M.mult t t'

  data _⊢_∈_⟶_ : (Γ : Con) → Is → Stack Γ Δ → Stack Γ Δ' → Set where
    Ty-ret : 
      {σ : Stack Γ Δ}{t : Tm Γ A}{t' : Tm Γ A} → 
      ⦃ t ≡ t' ⦄ → 
      Γ ⊢ ret ∈ σ ∷ t ⟶ σ ∷ t'
    Ty-⨾ : 
      ∀ {I : Instr}{σ : Stack Γ Δ}{σ' : Stack Γ Δ'}{σ'' : Stack Γ Δ''} →  
      Γ ⊢ᵢ I ∈ σ ⟶ σ' → Γ ⊢ ins ∈ σ' ⟶ σ'' → 
      Γ ⊢ I ⨾ ins ∈ σ ⟶ σ''


mutual 
  data ⊢_==_ : Val → {A : Ty} → Tm · A → Set where
    Ty-unit : ⊢ <> == M.unit
    Ty-nat : ∀{n}{t : Tm · Nat} → ⦃ t ≡ M.lit n ⦄ → ⊢ lit-n n == t
    Ty-clo : 
      {σ : Stack (Γ ∷ A) Δ}{t : Tm (Γ ∷ A) B}{γ : Sub · Γ}
      {body : Tm · (A ⇒ B)} → 
      env ⊨ Γ as γ → 
      (Γ ∷ A) ⊢ ins ∈ · ⟶ σ ∷ t →
      ⦃ M.lam (t [ ↑ γ ]) ≡ body ⦄ →   
      ⊢ < env , ins > == body

  data _⊨_as_ : Env → (Γ : Con) → Sub · Γ → Set where
    Env-nil : · ⊨ · as ⊘
    Env-cons : 
      {t : Tm · A}{γ : Sub · Γ} → 
      ⊢ v == t → 
      env ⊨ Γ as γ → 
      (env ∷ v) ⊨ (Γ ∷ A) as (γ ▻ t)

data _⊢[_⊨_] {γ : Sub · Γ} (env⊨ : env ⊨ Γ as γ) : Env → Stack Γ Δ → Set where
  St-nil : env⊨ ⊢[ · ⊨ · ]
  St-cons : 
    {σ : Stack Γ Δ}{t : Tm Γ A} → 
    env⊨ ⊢[ stack ⊨ σ ] → 
    ⊢ v == (t [ γ ]) → 
    env⊨ ⊢[ stack ∷ v ⊨ σ ∷ t ]

data _⊢ᵣ_∈_⟶_ : {γ : Sub · Γ} (env⊨ : env ⊨ Γ as γ) → Frame → {A : Ty} → Tm Γ A → Ty → Set where
  Frame-nil : {t : Tm · A} → Env-nil ⊢ᵣ · ∈ t ⟶ A
  Frame-cons : 
    {σ : Stack Γ Δ}{σ' : Stack Γ Δ'}
    {s : Tm Γ A}{t : Tm Γ B}{t' : Tm Γ' B}
    {γ : Sub · Γ}{γ' : Sub · Γ'}
    {env⊨' : env' ⊨ Γ' as γ'} → 
    env⊨' ⊢ᵣ fr ∈ t' ⟶ A₀ → 
    Γ ⊢ ins ∈ σ ∷ s ⟶ σ' ∷ t →
    (env⊨ : env ⊨ Γ as γ) → 
    env⊨ ⊢[ stack ⊨ σ ] →
    ⦃ t [ γ ] ≡ t' [ γ' ] ⦄ →  
    env⊨ ⊢ᵣ fr ∷< env , stack , ins > ∈ s ⟶ A₀


record WF-Config (A₀ : Ty) (c : Config) : Set where
  constructor well-formed
  field
    {Γc Γc' Δc Δc'} : Con
    {Ac} : Ty
    {σ} : Stack Γc Δc
    {σ'} : Stack Γc Δc'
    {γ} : Sub · Γc
    {γ'} : Sub · Γc'
    {t} : Tm Γc Ac
    {t'} : Tm Γc' Ac
    {ee} : Env
    {ty-env'} : ee ⊨ Γc' as γ'
    ty-ins : Γc ⊢ (Config.ins c) ∈ σ ⟶ σ' ∷ t
    ty-env : (Config.env c) ⊨ Γc as γ
    ty-st : ty-env ⊢[ (Config.stack c) ⊨ σ ]
    ty-fr : ty-env' ⊢ᵣ (Config.fr c) ∈ t' ⟶ A₀
    eq : t [ γ ] ≡ t' [ γ' ] 

mutual
  transform-i : 
    {σ : Stack Γ Δ}{σ' : Stack Γ Δ'}{ins : Instr} → 
    Γ ⊢ᵢ ins ∈ σ ⟶ σ' → Γ T.⊢ᵢ ins ∈ Δ ⟶ Δ'
  transform-i Ty-pop = T.Ty-pop
  transform-i Ty-swap = T.Ty-swap
  transform-i Ty-app = T.Ty-app
  transform-i Ty-unit = T.Ty-unit
  transform-i (Ty-var x) = T.Ty-var x
  transform-i (Ty-st x) = T.Ty-st x
  transform-i (Ty-pushc ins) = T.Ty-pushc (transform ins)
  transform-i (Ty-clo ⦃ eq-e ⦄ eq eq-n ty-ins) = T.Ty-clo eq-e eq-n (transform ty-ins)
  transform-i (Ty-lit n) = T.Ty-lit n
  transform-i Ty-suc = T.Ty-suc
  transform-i (Ty-rec iZ iS) = T.Ty-rec (transform iZ) (transform iS)
  transform-i Ty-add = T.Ty-add
  transform-i Ty-mult = T.Ty-mult

  transform : 
    {σ : Stack Γ Δ}{σ' : Stack Γ Δ'}{ins : Is} → 
    Γ ⊢ ins ∈ σ ⟶ σ' → Γ T.⊢ ins ∈ Δ ⟶ Δ'
  transform Ty-ret = T.Ty-ret
  transform (Ty-⨾ i ins) = T.Ty-⨾ (transform-i i) (transform ins)

mutual
  transform-v : {t : Tm · A} → ⊢ v == t → T.⊢ v ∈ A
  transform-v Ty-unit = T.Ty-unit
  transform-v Ty-nat = T.Ty-nat
  transform-v (Ty-clo env ins) = T.Ty-clo (transform-env env) (transform ins)

  transform-env : {γ : Sub · Γ} → env ⊨ Γ as γ → env T.⊨ Γ
  transform-env Env-nil = T.Env-nil
  transform-env (Env-cons v env) = T.Env-cons (transform-v v) (transform-env env)

transform-st : 
  {γ : Sub · Γ}{env⊨ : env ⊨ Γ as γ}{σ : Stack Γ Δ} → 
  env⊨ ⊢[ stack ⊨ σ ] → stack T.⊨ Δ 
transform-st St-nil = T.Env-nil
transform-st (St-cons sta v) = T.Env-cons (transform-v v) (transform-st sta)

transform-fr : 
  {γ : Sub · Γ}{t : Tm Γ A}
  {env⊨ : env ⊨ Γ as γ} → 
  env⊨ ⊢ᵣ fr ∈ t ⟶ A₀ →
  Γ T.⊢ᵣ fr ∈ A ⟶ A₀
transform-fr Frame-nil = T.Frame-nil
transform-fr (Frame-cons pf ins env⊨ stack) = 
  T.Frame-cons (transform-fr pf) (transform ins) (transform-env env⊨) (transform-st stack)

transform-c : {c : Config} → WF-Config A₀ c → T.WF-Config A₀ c
transform-c (well-formed ty-ins ty-env ty-st ty-fr eq) = 
  T.well-formed (transform ty-ins) (transform-env ty-env) (transform-st ty-st) (transform-fr ty-fr)

find-var : {γ : Sub · Γ} → (x : Var Γ A) → env ⊨ Γ as γ → Σ Val (λ v → [ x ↦ v ]∈ env)
find-var {env = env ∷ v} v₀ (Env-cons tv ty-env) = v , hd
find-var {env = env ∷ _} (vs x) (Env-cons _ ty-env) =
  let (v , pf) = find-var x ty-env in 
    v , tl pf

find-var-st : {γ : Sub · Γ}{σ : Stack Γ Δ}{env⊨ : env ⊨ Γ as γ} → 
  (x : Var Δ A) → env⊨ ⊢[ stack ⊨ σ ] → Σ Val (λ v → [ x ↦ v ]∈ stack) 
find-var-st {stack = stack ∷ v} v₀ (St-cons ty-st ta) = v , hd
find-var-st {stack = stack ∷ v} (vs x) (St-cons ty-st ta) = 
  let (v , pf) = find-var-st x ty-st in 
    v , tl pf
  
ty-[↦]∈ : {γ : Sub · Γ}{x : Var Γ A} → env ⊨ Γ as γ → [ x ↦ v ]∈ env → ⊢ v == ((M.var x) [ γ ])
ty-[↦]∈ (Env-cons tv ty-env) hd = tv
ty-[↦]∈ (Env-cons tv ty-env) (tl tx) = ty-[↦]∈ ty-env tx

st-[↦]∈ : 
  {γ : Sub · Γ}{env⊨ : env ⊨ Γ as γ}{σ : Stack Γ Δ}{x : Var Δ A} → 
  env⊨ ⊢[ stack ⊨ σ ] → [ x ↦ v ]∈ stack → ⊢ v == ((find-st x σ) [ γ ])
st-[↦]∈ (St-cons ty-st tv) hd = tv
st-[↦]∈ (St-cons ty-st tv) (tl tx) = st-[↦]∈ ty-st tx

⊨++ : ∀{Δ₁ Δ₂} →
  {γ : Sub · Γ}{env⊨ : env ⊨ Γ as γ} → 
  {σ : Stack Γ Δ}{σ₁ : Stack Γ Δ₁}{σ₂ : Stack Γ Δ₂} → 
  ⦃ eq : Δ ≡ (Δ₁ ++ Δ₂) ⦄ → 
  env⊨ ⊢[ stack ⊨ σ ] → 
  σ ≡ subst (λ z → Stack Γ z) (sym eq) (σ₁ ++s σ₂) → 
  Σ Env (λ s1 → Σ Env (λ s2 → 
    stack ≡ (s1 ⋈e s2) × 
    env⊨ ⊢[ s1 ⊨ σ₁ ] × 
    env⊨ ⊢[ s2 ⊨ σ₂ ]))
⊨++ {stack = stack} {σ₂ = ·} ⦃ refl ⦄ ty-st refl = stack , · , refl , ty-st , St-nil
⊨++ {stack = stack ∷ v} {σ₂ = σ₂ ∷ t} ⦃ refl ⦄ (St-cons ty-st tv) refl 
  with ⊨++ {σ₂ = σ₂} ty-st refl 
... | s1 , s2 , refl , ty-s1 , ty-s2 = s1 , s2 ∷ v , refl , ty-s1 , St-cons ty-s2 tv

⊨-len : ∀{n} → 
  {γ : Sub · Γ}{env⊨ : env ⊨ Γ as γ}{σ : Stack Γ Δ} → 
  env⊨ ⊢[ stack ⊨ σ ] → len-C Δ ≡ n → len-E stack ≡ n
⊨-len St-nil refl = refl
⊨-len (St-cons ty-st x) refl = cong suc (⊨-len ty-st refl)

⋈e⊨++ : 
  ∀{Δ₁ Δ₂ s1 s2} →
  {γ : Sub · Γ}{env⊨ : env ⊨ Γ as γ} →
  {σ : Stack Γ Δ}{σ₁ : Stack Γ Δ₁}{σ₂ : Stack Γ Δ₂} →
  ⦃ eq : Δ ≡ (Δ₁ ++ Δ₂) ⦄ → 
  env⊨ ⊢[ stack ⊨ σ ] → 
  σ ≡ subst (λ z → Stack Γ z) (sym eq) (σ₁ ++s σ₂) → 
  stack ≡ (s1 ⋈e s2) → 
  len-C Δ₂ ≡ len-E s2 → 
  env⊨ ⊢[ s1 ⊨ σ₁ ] × s2 ⊨ Δ₂ as (to-sub σ₂ ∘ γ)
⋈e⊨++ {Δ₂ = ·} {s2 = ·} {σ₂ = ·} ⦃ refl ⦄ ty-st refl refl refl = ty-st , Env-nil
⋈e⊨++ {Δ₂ = Δ₂ ∷ A} {s2 = s2 ∷ v} {σ₂ = σ₂ ∷ t} ⦃ refl ⦄ (St-cons ty-st tv) refl refl eq-len =
  let (ty-s1 , ty-s2) = ⋈e⊨++ {σ₂ = σ₂} ty-st refl refl (suc-inj eq-len) in  
  ty-s1 , Env-cons tv ty-s2

Progress : WF-Config A₀ c → (Σ Val (λ v → c ⇓₀ v , zero)) ⊎ (Σ Config (λ c' → c ⟶ c'))
Progress {c = ⟨ ins , env , stack ∷ v , · ⟩} (well-formed Ty-ret ty-env (St-cons ty-st tv) Frame-nil eq) = 
  inj₁ (v , finish)
Progress (well-formed Ty-ret ty-env (St-cons ty-st x₂) (Frame-cons ty-fr x env⊨ x₁) eq) = 
  inj₂ (_ , Op-ret)
Progress (well-formed (Ty-⨾ Ty-pop ty-ins) ty-env (St-cons ty-st _) ty-fr eq) = 
  inj₂ (_ , Op-pop)
Progress (well-formed (Ty-⨾ Ty-swap ty-ins) ty-env (St-cons (St-cons ty-st x₁) x) ty-fr eq) = 
  inj₂ (_ , Op-swap)
Progress (well-formed (Ty-⨾ Ty-app ty-ins) ty-env (St-cons (St-cons ty-st (Ty-clo x₁ x₂)) x) ty-fr eq) = 
  inj₂ (_ , Op-app)
Progress (well-formed (Ty-⨾ Ty-unit ty-ins) ty-env ty-st ty-fr eq) = 
  inj₂ (_ , Op-unit)
Progress (well-formed (Ty-⨾ (Ty-var x) ty-ins) ty-env ty-st ty-fr eq) = 
  inj₂ (_ , Op-var (π₂ (find-var x ty-env)))
Progress (well-formed (Ty-⨾ (Ty-st x) ty-ins) ty-env ty-st ty-fr eq) = 
  inj₂ (_ , Op-st (π₂ (find-var-st x ty-st)))
Progress (well-formed (Ty-⨾ (Ty-pushc ty-ins') ty-ins) ty-env ty-st ty-fr eq) = 
  inj₂ (_ , Op-pushc)
Progress (well-formed (Ty-⨾ (Ty-clo {σ₁ = σ₁} {σ₂} ⦃ eq-Δ ⦄ eq-s eq-n ty-ins') ty-ins) ty-env ty-st ty-fr eq) 
  with ⊨++ {σ₁ = σ₁} {σ₂} ⦃ eq-Δ ⦄ ty-st eq-s
... | s1 , s2 , eq , ty-s1 , ty-s2 = 
  inj₂ (_ , Op-clo eq (⊨-len ty-s2 eq-n) ) 
Progress (well-formed (Ty-⨾ (Ty-lit n) ty-ins) ty-env ty-st ty-fr eq) = 
  inj₂ (_ , Op-lit n)
Progress (well-formed (Ty-⨾ Ty-suc ty-ins) ty-env (St-cons ty-st Ty-nat) ty-fr eq) = 
  inj₂ (_ , Op-suc)
Progress (well-formed (Ty-⨾ (Ty-rec tZ tS) ty-ins) ty-env (St-cons ty-st (Ty-nat {n = zero})) ty-fr eq) = 
  inj₂ (_ , Op-recZ)
Progress (well-formed (Ty-⨾ (Ty-rec tZ tS) ty-ins) ty-env (St-cons ty-st (Ty-nat {n = suc n})) ty-fr eq) = 
  inj₂ (_ , Op-recS n)
Progress (well-formed (Ty-⨾ Ty-add ty-ins) ty-env (St-cons (St-cons ty-st Ty-nat) Ty-nat) ty-fr eq) = 
  inj₂ (_ , Op-add _ _)
Progress (well-formed (Ty-⨾ Ty-mult ty-ins) ty-env (St-cons (St-cons ty-st Ty-nat) Ty-nat) ty-fr eq) = 
  inj₂ (_ , Op-mult _ _)

~λ≡ : {t t' : Tm · A} → t ≡ t' → t .~fun tt ≡ t' .~fun tt
~λ≡ refl = refl

~λ-ext : {t t' : Tm · A} → t .~fun tt ≡ t' .~fun tt → t ≡ t'
~λ-ext pf = cong ~λ (ext-tt pf)

Preservation : c ⟶ c' → WF-Config A₀ c → WF-Config A₀ c'
Preservation Op-pop (well-formed (Ty-⨾ Ty-pop ty-ins) ty-env (St-cons ty-st _) ty-fr eq) = 
  well-formed ty-ins ty-env ty-st ty-fr eq
Preservation Op-swap (well-formed (Ty-⨾ Ty-swap ty-ins) ty-env (St-cons (St-cons ty-st x₁) x) ty-fr eq) = 
  well-formed ty-ins ty-env (St-cons (St-cons ty-st x) x₁) ty-fr eq

Preservation Op-app (well-formed (Ty-⨾ Ty-app ty-ins) ty-env (St-cons (St-cons ty-st (Ty-clo ty-env' ty-ins' ⦃ eq-f ⦄)) tv) ty-fr eq) = 
  well-formed ty-ins' (Env-cons tv ty-env') St-nil (Frame-cons ty-fr ty-ins ty-env ty-st ⦃ eq ⦄ ) 
  (~λ-ext (cong-app (~λ≡ eq-f) _))

{-

cong-app {f = f .~fun } ? (t' .~fun (γ tt)) 
Not an easy problem.

eq-f : lam (t [ ↑ γ ]) = t1

goal: t [ γ , t'[γ] ] ≡ (app (t1 t')) [ γ ]
where
  (app t1 t') [ γ ]
    = (t1 [ γ ]) (t' [ γ ])
    { key step to evaluate is here }
    = (lam t [↑γ]) (t' [ γ ])
    = (t [ ↑γ ]) [ id , t' [ γ ] ]
    = t [ γ , t' [ γ ]]

t₁ .~fun (γ₁ tt) (t' .~fun (γ₁ tt))

(λ a → t .~fun (γ tt , a)) ≡
t₁ .~fun (γ₁ tt)

so, t₁ .~fun (γ₁ tt) (t' .~fun (γ₁ tt))
= t .~fun (γ tt , (t' .~fun (γ₁ tt)))

exactly what we want.

-}

Preservation Op-unit (well-formed (Ty-⨾ Ty-unit ty-ins) ty-env ty-st ty-fr eq) = 
  well-formed ty-ins ty-env (St-cons ty-st Ty-unit) ty-fr eq
Preservation Op-pushc (well-formed (Ty-⨾ (Ty-pushc ty-ins') ty-ins) ty-env ty-st ty-fr eq) = 
  well-formed ty-ins ty-env (St-cons ty-st (Ty-clo ty-env ty-ins')) ty-fr eq

Preservation (Op-clo pf eq-n) (well-formed (Ty-⨾ (Ty-clo eq-s eq-n' ty-ins') ty-ins) ty-env ty-st ty-fr eq) =
  let (ty-s1 , ty-s2) = ⋈e⊨++ ty-st eq-s pf (trans eq-n' (sym eq-n)) in
  well-formed ty-ins ty-env (St-cons ty-s1 (Ty-clo ty-s2 ty-ins')) ty-fr eq

Preservation Op-ret (well-formed (Ty-ret ⦃ refl ⦄) ty-env (St-cons {v = v} ty-st tv) (Frame-cons ty-fr ty-ins' ty-env' ty-st' ⦃ eq' ⦄) eq) = 
  well-formed ty-ins' ty-env' (St-cons ty-st' (subst (λ z → ⊢ v == z) eq tv)) ty-fr eq'
Preservation (Op-var tx) (well-formed (Ty-⨾ (Ty-var x) ty-ins) ty-env ty-st ty-fr eq) = 
  well-formed ty-ins ty-env (St-cons ty-st (ty-[↦]∈ ty-env tx)) ty-fr eq
Preservation (Op-st tx) (well-formed (Ty-⨾ (Ty-st x) ty-ins) ty-env ty-st ty-fr eq) = 
  well-formed ty-ins ty-env (St-cons ty-st (st-[↦]∈ ty-st tx)) ty-fr eq
Preservation (Op-lit n) (well-formed (Ty-⨾ (Ty-lit n) ty-ins) ty-env ty-st ty-fr eq) = 
  well-formed ty-ins ty-env (St-cons ty-st Ty-nat) ty-fr eq

Preservation Op-suc (well-formed (Ty-⨾ Ty-suc ty-ins) ty-env (St-cons ty-st (Ty-nat ⦃ eq-n ⦄)) ty-fr eq) = 
  well-formed ty-ins ty-env (St-cons ty-st (Ty-nat ⦃ cong ~λ (ext-tt (cong suc (cong-app (cong ~fun eq-n) tt))) ⦄)) ty-fr eq

Preservation Op-recZ (well-formed (Ty-⨾ (Ty-rec {tZ = tZ} {tS = tS} ty-Z ty-S) ty-ins) ty-env (St-cons ty-st (Ty-nat {n = zero} ⦃ eq-n ⦄)) ty-fr eq) = 
  well-formed ty-Z ty-env St-nil (Frame-cons ty-fr ty-ins ty-env ty-st ⦃ eq ⦄ ) 
  (M.rec-Z eq-n)

Preservation (Op-recS n) (well-formed (Ty-⨾ (Ty-rec {tZ = tZ} {tS = tS} {n = tn} ty-Z ty-S) ty-ins) ty-env (St-cons ty-st (Ty-nat {n = suc n} {t = t} ⦃ eq-n ⦄)) ty-fr eq) = 
  well-formed (Ty-⨾ (Ty-rec ty-Z ty-S) (Ty-⨾ (Ty-app {t = M.lam (tS [ ↑ (✧ ▻ M.lit n) ])}) Ty-ret)) 
    ty-env 
    (St-cons (St-cons St-nil (Ty-clo (Env-cons Ty-nat ty-env) ty-S)) (Ty-nat {n = n})) 
    (Frame-cons ty-fr ty-ins ty-env ty-st ⦃ eq ⦄) 
    (M.rec-S eq-n)

Preservation (Op-add m n) (well-formed (Ty-⨾ Ty-add ty-ins) ty-env (St-cons (St-cons ty-st (Ty-nat {t = t} ⦃ eq1 ⦄)) (Ty-nat ⦃ eq2 ⦄)) ty-fr eq) = 
  well-formed ty-ins ty-env (St-cons ty-st (Ty-nat ⦃ ~λ-ext (cong₂ _+_ (~λ≡ eq1) (~λ≡ eq2)) ⦄)) ty-fr eq

Preservation (Op-mult m n) (well-formed (Ty-⨾ Ty-mult ty-ins) ty-env (St-cons (St-cons ty-st (Ty-nat {t = t} ⦃ eq1 ⦄)) (Ty-nat ⦃ eq2 ⦄)) ty-fr eq) =
   well-formed ty-ins ty-env (St-cons ty-st (Ty-nat ⦃ ~λ-ext (cong₂ _*_ (~λ≡ eq1) (~λ≡ eq2)) ⦄)) ty-fr eq

Preservation* : c ⟶* c' → WF-Config A₀ c → WF-Config A₀ c'
Preservation* ε wf = wf
Preservation* (a ∷ σ) wf = Preservation* σ (Preservation a wf)

Termination : WF-Config A₀ c → (Σ Val (λ v → c ⇓ v))
Termination wf = H.Termination (transform-c wf)

-- Expected result according to specification
fr-res : ∀{γ : Sub · Γ}{env⊨ : env ⊨ Γ as γ}{t : Tm Γ A} → env⊨ ⊢ᵣ fr ∈ t ⟶ A₀ → Tm · A₀
fr-res (Frame-nil {t = t}) = t
fr-res (Frame-cons fr x env⊨ x₁) = fr-res fr

Exp : WF-Config A₀ c → Tm · A₀
Exp (well-formed ty-ins ty-env ty-st ty-fr eq) = fr-res ty-fr

Preservation-Exp : (a : c ⟶ c') → (wf : WF-Config A₀ c) → Exp (Preservation a wf) ≡ Exp wf
Preservation-Exp Op-pop (well-formed (Ty-⨾ Ty-pop ty-ins) ty-env (St-cons ty-st _) ty-fr eq) = refl
Preservation-Exp Op-swap (well-formed (Ty-⨾ Ty-swap ty-ins) ty-env (St-cons (St-cons ty-st x₁) x) ty-fr eq) = refl
Preservation-Exp Op-app (well-formed (Ty-⨾ Ty-app ty-ins) ty-env (St-cons (St-cons ty-st (Ty-clo ty-env' ty-ins' ⦃ eq-f ⦄)) tv) ty-fr eq) = refl
Preservation-Exp Op-unit (well-formed (Ty-⨾ Ty-unit ty-ins) ty-env ty-st ty-fr eq) = refl
Preservation-Exp Op-pushc (well-formed (Ty-⨾ (Ty-pushc ty-ins') ty-ins) ty-env ty-st ty-fr eq) = refl
Preservation-Exp (Op-clo pf eq-n) (well-formed (Ty-⨾ (Ty-clo eq-s eq-n' ty-ins') ty-ins) ty-env ty-st ty-fr eq) = refl
Preservation-Exp Op-ret (well-formed (Ty-ret ⦃ refl ⦄) ty-env (St-cons {v = v} ty-st tv) (Frame-cons ty-fr ty-ins' ty-env' ty-st' ⦃ eq' ⦄) eq) = refl
Preservation-Exp (Op-var tx) (well-formed (Ty-⨾ (Ty-var x) ty-ins) ty-env ty-st ty-fr eq) = refl
Preservation-Exp (Op-st tx) (well-formed (Ty-⨾ (Ty-st x) ty-ins) ty-env ty-st ty-fr eq) = refl
Preservation-Exp (Op-lit n) (well-formed (Ty-⨾ (Ty-lit n) ty-ins) ty-env ty-st ty-fr eq)  = refl
Preservation-Exp Op-suc (well-formed (Ty-⨾ Ty-suc ty-ins) ty-env (St-cons ty-st (Ty-nat ⦃ eq-n ⦄)) ty-fr eq) = refl
Preservation-Exp Op-recZ (well-formed (Ty-⨾ (Ty-rec {tZ = tZ} {tS = tS} ty-Z ty-S) ty-ins) ty-env (St-cons ty-st (Ty-nat {n = zero} ⦃ eq-n ⦄)) ty-fr eq) = refl
Preservation-Exp (Op-recS n) (well-formed (Ty-⨾ (Ty-rec {tZ = tZ} {tS = tS} {n = tn} ty-Z ty-S) ty-ins) ty-env (St-cons ty-st (Ty-nat {n = suc n} {t = t} ⦃ eq-n ⦄)) ty-fr eq) = refl
Preservation-Exp (Op-add m n) (well-formed (Ty-⨾ Ty-add ty-ins) ty-env (St-cons (St-cons ty-st (Ty-nat {t = t} ⦃ eq1 ⦄)) (Ty-nat ⦃ eq2 ⦄)) ty-fr eq) = refl
Preservation-Exp (Op-mult m n) (well-formed (Ty-⨾ Ty-mult ty-ins) ty-env (St-cons (St-cons ty-st (Ty-nat {t = t} ⦃ eq1 ⦄)) (Ty-nat ⦃ eq2 ⦄)) ty-fr eq) = refl

Partial-Correctness : c ⇓ v → (wf : WF-Config A₀ c) → ⊢ v == Exp wf
Partial-Correctness (halt σ) wf = aux σ wf
  where
    aux : c ⟶* ⟨ ret , env , stack ∷ v , · ⟩ → (wf : WF-Config A₀ c) → ⊢ v == Exp wf
    aux ε (well-formed (Ty-ret ⦃ refl ⦄) ty-env (St-cons ty-st tv) Frame-nil refl) = tv
    aux {v = v} (a ∷ σ) wf = subst (λ z → ⊢ v == z) (Preservation-Exp a wf) (aux σ (Preservation a wf))

Total-Correctness : (wf : WF-Config A₀ c) → Σ Val (λ v → (c ⇓ v) × ⊢ v == Exp wf)
Total-Correctness wf = 
  let (v , σ) = Termination wf in
    v , σ , (Partial-Correctness σ wf)

Total-Correctness-Prog : 
  {σ : Stack · Δ}{t : Tm · A} → 
  · ⊢ ins ∈ · ⟶ (σ ∷ t) → Σ Val (λ v → ⟨ ins , · , · , · ⟩ ⇓ v × ⊢ v == t)
Total-Correctness-Prog ty-ins = Total-Correctness (well-formed ty-ins Env-nil St-nil Frame-nil refl)


