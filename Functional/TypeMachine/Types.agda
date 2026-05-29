module Functional.TypeMachine.Types where

open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.Sum hiding (swap)
open import Data.Nat
open import Relation.Binary.PropositionalEquality 

open import Basic
open import Context
open import Functional.Syntax

{- Typed SECD machine -}

private variable
  Γ Γ' Γ'' Δ Δ' Δ'' : Con
  A A' B B' C C' A₀ : Ty
  ins ins' ins'' : Is
  v v' v'' : Val
  env env' env'' stack stack' stack'' : Env
  fr fr' : Frame
  c c' c'' c₀ : Config

infix 10 _⊢ᵢ_∈_⟶_

{- Typing instructions -}
mutual
  data _⊢ᵢ_∈_⟶_ : Con → Instr → Con → Con → Set where
    Ty-pop : Γ ⊢ᵢ pop ∈ Δ ∷ A ⟶ Δ
    Ty-swap : Γ ⊢ᵢ swap ∈ Δ ∷ A ∷ B ⟶ Δ ∷ B ∷ A
    Ty-app : Γ ⊢ᵢ app ∈ Δ ∷ (A ⇒ B) ∷ A ⟶ Δ ∷ B
    Ty-unit : Γ ⊢ᵢ unit ∈ Δ ⟶ Δ ∷ One
    Ty-var : (x : Var Γ A) → Γ ⊢ᵢ var x ∈ Δ ⟶ Δ ∷ A
    Ty-st : (x : Var Δ A) → Γ ⊢ᵢ st x ∈ Δ ⟶ Δ ∷ A
    Ty-pushc : (Γ ∷ A) ⊢ ins ∈ · ⟶ (Δ' ∷ B) → Γ ⊢ᵢ pushc ins ∈ Δ ⟶ Δ ∷ (A ⇒ B)
    Ty-clo : ∀{n Δ₁ Δ₂} → 
      Δ ≡ (Δ₁ ++ Δ₂) → 
      len-C Δ₂ ≡ n → 
      (Δ₂ ∷ A) ⊢ ins ∈ · ⟶ (Δ' ∷ B) → 
      Γ ⊢ᵢ clo n ins ∈ Δ ⟶ Δ₁ ∷ (A ⇒ B)
    Ty-lit : (n : ℕ) → Γ ⊢ᵢ lit n ∈ Δ ⟶ Δ ∷ Nat
    Ty-suc : Γ ⊢ᵢ suc ∈ Δ ∷ Nat ⟶ Δ ∷ Nat
    Ty-rec : 
      Γ ⊢ ins ∈ · ⟶ (Δ ∷ A) → 
      (Γ ∷ Nat ∷ A) ⊢ ins' ∈ · ⟶ (Δ' ∷ A) → 
      Γ ⊢ᵢ rec ins ins' ∈ Δ'' ∷ Nat ⟶ Δ'' ∷ A
    Ty-add : Γ ⊢ᵢ add ∈ Δ ∷ Nat ∷ Nat ⟶ Δ ∷ Nat
    Ty-mult : Γ ⊢ᵢ mult ∈ Δ ∷ Nat ∷ Nat ⟶ Δ ∷ Nat

  data _⊢_∈_⟶_ : Con → Is → Con → Con → Set where
    Ty-ret : Γ ⊢ ret ∈ (Δ ∷ A) ⟶ (Δ ∷ A)
    Ty-⨾ : ∀{I : Instr} → 
      Γ ⊢ᵢ I ∈ Δ ⟶ Δ' → Γ ⊢ ins ∈ Δ' ⟶ Δ'' → 
      Γ ⊢ I ⨾ ins ∈ Δ ⟶ Δ''

{- Typing the machine -}
mutual 
  data ⊢_∈_ : Val → Ty → Set where
    Ty-unit : ⊢ <> ∈ One
    Ty-nat : ∀{n} → ⊢ lit-n n ∈ Nat
    Ty-clo : 
      env ⊨ Γ → (Γ ∷ A) ⊢ ins ∈ · ⟶ (Δ ∷ B) →  
      ⊢ < env , ins > ∈ A ⇒ B

  data _⊨_ : Env → Con → Set where
    Env-nil : · ⊨ ·
    Env-cons : ⊢ v ∈ A → env ⊨ Γ → (env ∷ v) ⊨ (Γ ∷ A)

data _⊢ᵣ_∈_⟶_ : Con → Frame → Ty → Ty → Set where
  Frame-nil : · ⊢ᵣ · ∈ A₀ ⟶ A₀
  Frame-cons : 
    Γ' ⊢ᵣ fr ∈ B ⟶ A₀ → 
    Γ ⊢ ins ∈ (Δ ∷ A) ⟶ (Δ' ∷ B) →
    env ⊨ Γ → 
    stack ⊨ Δ →
    Γ ⊢ᵣ fr ∷< env , stack , ins > ∈ A ⟶ A₀

data WF-Config (A₀ : Ty) : Config → Set where
  well-formed : 
    Γ ⊢ ins ∈ Δ ⟶ (Δ' ∷ A) →
    env ⊨ Γ → 
    stack ⊨ Δ →
    Γ' ⊢ᵣ fr ∈ A ⟶ A₀ → 
    WF-Config A₀ (⟨ ins , env , stack , fr ⟩) 

{- Type safety -}

find-var : (x : Var Γ A) → env ⊨ Γ → Σ Val (λ v → [ x ↦ v ]∈ env)
find-var {env = env ∷ v} v₀ (Env-cons tv ty-env) = v , hd
find-var {env = env ∷ _} (vs x) (Env-cons _ ty-env) with find-var x ty-env
... | v , pf = v , (tl pf)

ty-[↦]∈ : ∀{x : Var Γ A} → env ⊨ Γ → [ x ↦ v ]∈ env → ⊢ v ∈ A
ty-[↦]∈ (Env-cons tv ty-env) hd = tv
ty-[↦]∈ (Env-cons _ ty-env) (tl tx) = ty-[↦]∈ ty-env tx

⊨-len : ∀{n} → env ⊨ Γ → len-C Γ ≡ n → len-E env ≡ n
⊨-len Env-nil refl = refl
⊨-len (Env-cons _ ty-env) refl = cong suc (⊨-len ty-env refl)

⊨++ : ∀{Δ₁ Δ₂} → 
  Δ ≡ (Δ₁ ++ Δ₂) → 
  stack ⊨ Δ → 
  Σ Env (λ s1 → Σ Env (λ s2 → stack ≡ (s1 ⋈e s2) × s1 ⊨ Δ₁ × s2 ⊨ Δ₂))
⊨++ {stack = stack} {Δ₂ = ·} refl ty-st = stack , · , refl , ty-st , Env-nil
⊨++ {stack = stack ∷ v} {Δ₂ = Δ₂ ∷ A} refl (Env-cons ta ty-st) 
  with ⊨++ {Δ₂ = Δ₂} refl ty-st 
... | s1 , s2 , refl , ty-s1 , ty-s2 = s1 , (s2 ∷ v) , refl , ty-s1 , Env-cons ta ty-s2

⋈e⊨++ : 
  ∀{Δ₁ Δ₂ s1 s2} → 
  stack ⊨ Δ →
  Δ ≡ (Δ₁ ++ Δ₂) →  
  stack ≡ (s1 ⋈e s2) → 
  len-C Δ₂ ≡ len-E s2 → 
  s1 ⊨ Δ₁ × s2 ⊨ Δ₂
⋈e⊨++ {Δ₂ = ·} {s2 = ·} ty-st refl refl refl = ty-st , Env-nil
⋈e⊨++ {Δ₂ = Δ₂ ∷ A} {s2 = s2 ∷ v} (Env-cons ta ty-st) refl refl eq-len = 
  let ind = ⋈e⊨++ ty-st refl refl (suc-inj eq-len) in
    π₁ ind , Env-cons ta (π₂ ind)

Preservation : c ⟶ c' → WF-Config A₀ c → WF-Config A₀ c'
Preservation Op-pop (well-formed (Ty-⨾ Ty-pop ty-ins) ty-env (Env-cons _ ty-st) ty-fr) = 
  well-formed ty-ins ty-env ty-st ty-fr
Preservation Op-swap (well-formed (Ty-⨾ Ty-swap ty-ins) ty-env (Env-cons ta (Env-cons tb ty-st)) ty-fr) = 
  well-formed ty-ins ty-env (Env-cons tb (Env-cons ta ty-st)) ty-fr
Preservation Op-app (well-formed (Ty-⨾ Ty-app ty-ins) ty-env (Env-cons ta (Env-cons (Ty-clo ty-env' ty-ins') ty-st)) ty-fr) = 
  well-formed ty-ins' (Env-cons ta ty-env') Env-nil (Frame-cons ty-fr ty-ins ty-env ty-st)
Preservation Op-unit (well-formed (Ty-⨾ Ty-unit ty-ins) ty-env ty-st ty-fr) = 
  well-formed ty-ins ty-env (Env-cons Ty-unit ty-st) ty-fr
Preservation Op-pushc (well-formed (Ty-⨾ (Ty-pushc ty-ins') ty-ins) ty-env ty-st ty-fr) = 
  well-formed ty-ins ty-env (Env-cons (Ty-clo ty-env ty-ins') ty-st) ty-fr
Preservation (Op-clo pf len<) (well-formed (Ty-⨾ (Ty-clo pf-c len<-c ty-ins') ty-ins) ty-env ty-st ty-fr) = 
  let ty-split = ⋈e⊨++ ty-st pf-c pf (trans len<-c (sym len<)) in  
    well-formed ty-ins ty-env (Env-cons (Ty-clo (π₂ ty-split) ty-ins') (π₁ ty-split)) ty-fr
Preservation Op-ret (well-formed Ty-ret ty-env (Env-cons ta ty-st) (Frame-cons ty-fr ty-ins' ty-env' ty-st')) = 
  well-formed ty-ins' ty-env' (Env-cons ta ty-st') ty-fr
Preservation (Op-var tx) (well-formed (Ty-⨾ (Ty-var x) ty-ins) ty-env ty-st ty-fr) = 
  well-formed ty-ins ty-env (Env-cons (ty-[↦]∈ ty-env tx) ty-st) ty-fr
Preservation (Op-st tx) (well-formed (Ty-⨾ (Ty-st x) ty-ins) ty-env ty-st ty-fr) = 
  well-formed ty-ins ty-env (Env-cons (ty-[↦]∈ ty-st tx) ty-st) ty-fr
Preservation (Op-lit n) (well-formed (Ty-⨾ (Ty-lit n) ty-ins) ty-env ty-st ty-fr) = 
  well-formed ty-ins ty-env (Env-cons Ty-nat ty-st) ty-fr
Preservation Op-suc (well-formed (Ty-⨾ Ty-suc ty-ins) ty-env (Env-cons Ty-nat ty-st) ty-fr) = 
  well-formed ty-ins ty-env (Env-cons Ty-nat ty-st) ty-fr
Preservation Op-recZ (well-formed (Ty-⨾ (Ty-rec tyZ tyS) ty-ins) ty-env (Env-cons Ty-nat ty-st) ty-fr) = 
  well-formed tyZ ty-env Env-nil (Frame-cons ty-fr ty-ins ty-env ty-st)
Preservation (Op-recS n) (well-formed (Ty-⨾ (Ty-rec tyZ tyS) ty-ins) ty-env (Env-cons Ty-nat ty-st) ty-fr) = 
  well-formed (Ty-⨾ (Ty-rec tyZ tyS) (Ty-⨾ Ty-app Ty-ret)) ty-env 
    (Env-cons Ty-nat (Env-cons (Ty-clo (Env-cons Ty-nat ty-env) tyS) Env-nil)) 
    (Frame-cons ty-fr ty-ins ty-env ty-st)
Preservation (Op-add m n) (well-formed (Ty-⨾ Ty-add ty-ins) ty-env (Env-cons Ty-nat (Env-cons Ty-nat ty-st)) ty-fr) = 
  well-formed ty-ins ty-env (Env-cons Ty-nat ty-st) ty-fr
Preservation (Op-mult m n) (well-formed (Ty-⨾ Ty-mult ty-ins) ty-env (Env-cons Ty-nat (Env-cons Ty-nat ty-st)) ty-fr) = 
  well-formed ty-ins ty-env (Env-cons Ty-nat ty-st) ty-fr

Progress : WF-Config A₀ c → (Σ Val (λ v → c ⇓₀ v , zero)) ⊎ (Σ Config (λ c' → c ⟶ c'))
Progress {c = ⟨ ins , env , stack ∷ v , · ⟩} (well-formed Ty-ret ty-env (Env-cons _ ty-st) Frame-nil) = 
  inj₁ (v , finish)
Progress (well-formed Ty-ret ty-env (Env-cons _ ty-st) (Frame-cons ty-fr x x₁ x₂)) = 
  inj₂ (_ , Op-ret)
Progress (well-formed (Ty-⨾ Ty-pop ty-ins) ty-env (Env-cons _ ty-st) ty-fr) = 
  inj₂ (_ , Op-pop)
Progress (well-formed (Ty-⨾ Ty-swap ty-ins) ty-env (Env-cons ta (Env-cons tb ty-st)) ty-fr) = 
  inj₂ (_ , Op-swap)
Progress (well-formed (Ty-⨾ Ty-app ty-ins) ty-env (Env-cons ta (Env-cons (Ty-clo ty-env' ty-ins') ty-st)) ty-fr) = 
  inj₂ (_ , Op-app)
Progress (well-formed (Ty-⨾ Ty-unit ty-ins) ty-env ty-st ty-fr) = 
  inj₂ (_ , Op-unit)
Progress (well-formed (Ty-⨾ (Ty-var x) ty-ins) ty-env ty-st ty-fr) = 
  inj₂ (_ , Op-var (π₂ (find-var x ty-env)))
Progress (well-formed (Ty-⨾ (Ty-st x) ty-ins) ty-env ty-st ty-fr) = 
  inj₂ (_ , Op-st (π₂ (find-var x ty-st)))
Progress (well-formed (Ty-⨾ (Ty-pushc ty-ins') ty-ins) ty-env ty-st ty-fr) = 
  inj₂ (_ , Op-pushc)
Progress (well-formed (Ty-⨾ (Ty-clo pf-c len<-c ty-ins') ty-ins) ty-env ty-st ty-fr)
  with ⊨++ pf-c ty-st
... | s1 , s2 , eq , ty-s1 , ty-s2 =  inj₂ (_ , (Op-clo eq (⊨-len ty-s2 len<-c)))
Progress (well-formed (Ty-⨾ (Ty-lit n) ty-ins) ty-env ty-st ty-fr) =
  inj₂ (_ , Op-lit n)
Progress (well-formed (Ty-⨾ Ty-suc ty-ins) ty-env (Env-cons Ty-nat ty-st) ty-fr) = 
  inj₂ (_ , Op-suc)
Progress (well-formed (Ty-⨾ (Ty-rec tyZ tyS) ty-ins) ty-env (Env-cons (Ty-nat {n = zero}) ty-st) ty-fr) = 
  inj₂ (_ , Op-recZ)
Progress (well-formed (Ty-⨾ (Ty-rec tyZ tyS) ty-ins) ty-env (Env-cons (Ty-nat {n = suc n}) ty-st) ty-fr) = 
  inj₂ (_ , Op-recS n)
Progress (well-formed (Ty-⨾ Ty-add ty-ins) ty-env (Env-cons (Ty-nat {n = n}) (Env-cons (Ty-nat {n = m}) ty-st)) ty-fr) = 
  inj₂ (_ , Op-add m n)
Progress (well-formed (Ty-⨾ Ty-mult ty-ins) ty-env (Env-cons (Ty-nat {n = n}) (Env-cons (Ty-nat {n = m}) ty-st)) ty-fr) = 
  inj₂ (_ , Op-mult m n)


Preservation* : c ⟶* c' → WF-Config A₀ c → WF-Config A₀ c'
Preservation* ε wf = wf
Preservation* (a ∷ σ) wf = Preservation* σ (Preservation a wf)

Preservation⇓ : c ⇓ v → (wf : WF-Config A₀ c) → ⊢ v ∈ A₀
Preservation⇓ (halt σ) wf with Preservation* σ wf
... | well-formed Ty-ret _ (Env-cons ta ty-st) Frame-nil = ta
