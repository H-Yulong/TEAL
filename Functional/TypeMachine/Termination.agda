module @0 Functional.TypeMachine.Termination where 

open import Data.Nat
open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.Sum hiding (swap)
open import Relation.Binary.PropositionalEquality 

open import Basic
open import Context
open import Functional.Syntax
open import Functional.TypeMachine.Types

private variable
  Γ Γ' Γ'' Δ Δ' Δ'' : Con
  A A' B B' C C' A₀ : Ty
  ins ins' ins'' : Is
  v v' v'' : Val
  env env' env'' stack stack' stack'' : Env
  fr fr' : Frame
  c c' c'' c₀ : Config

{- Biorthogonality -}

-- 1. Join operation
_⟫_ : Is → Is → Is
ret ⟫ ins' = ins'
(i ⨾ ins) ⟫ ins' = i ⨾ (ins ⟫ ins')

_⋈c_ : Is × Env → Is × Env × Env × Frame → Config
(ins , stack) ⋈c (ins' , env' , stack' , fr') = ⟨ (ins ⟫ ins') , env' , (stack' ⋈e stack) , fr' ⟩

-- 2. Observation: the machine halts for the current call frame.
-- Implemented as a trace that never goes below the current call frame.
-- Some equalities are propositional, to avoid the green slime.
record Halt-F (c : Config) : Set where
  constructor halt-f
  field
    {env₀ dump} : Env
    {res} : Val
    {fr₀} : Frame
    trace : c ⟶* ⟨ ret , env₀ , (dump ∷ res) , fr₀ ⟩
    nb : Not-below (Config.fr c) trace
    ⦃ eq-env ⦄ : Config.env c ≡ env₀
    ⦃ eq-fr ⦄  : Config.fr c ≡ fr₀

open Halt-F using (trace)

-- Properties of the Halt-F observation.
halt-cons : c ⟶ c' → c' ⇓ v → c ⇓ v
halt-cons a (halt σ) = halt (a ∷ σ)

trace-rw : (hf : Halt-F c) → c ⟶* ⟨ ret , Config.env c , (Halt-F.dump hf ∷ Halt-F.res hf) , Config.fr c ⟩
trace-rw (halt-f trace nb ⦃ refl ⦄ ⦃ refl ⦄) = trace

nb-rw : (hf : Halt-F c) → Not-below (Config.fr c) (trace-rw hf)
nb-rw (halt-f trace nb ⦃ refl ⦄ ⦃ refl ⦄) = nb

Partial-Halt : 
  (σ : ⟨ ins , env , stack , fr ⟩ ⟶* ⟨ ret , env' , stack' ∷ v , fr' ⟩) →
  Not-below fr' σ →
  (pf : fr' ≤ᵣ fr) → 
  ⟨ ins , env , stack , dropᵣ fr' fr pf ⟩ ⇓ v
Partial-Halt ε nb zero = halt ε
Partial-Halt ε nb (more pf) = absurd (≤ᵣ-cons-neq pf)
Partial-Halt (Op-pop ∷ σ) (fr< , nb) pf = halt-cons Op-pop (Partial-Halt σ nb pf)
Partial-Halt (Op-swap ∷ σ) (fr< , nb) pf = halt-cons Op-swap (Partial-Halt σ nb pf)
Partial-Halt (Op-app ∷ σ) (fr< , nb) pf = halt-cons Op-app (Partial-Halt σ nb (more pf))
Partial-Halt (Op-unit ∷ σ) (fr< , nb) pf = halt-cons Op-unit (Partial-Halt σ nb pf)
Partial-Halt (Op-pushc ∷ σ) (fr< , nb) pf = halt-cons Op-pushc (Partial-Halt σ nb pf)
Partial-Halt (Op-clo pfc len< ∷ σ) (fr< , nb) pf = halt-cons (Op-clo pfc len<) (Partial-Halt σ nb pf)
Partial-Halt (Op-ret ∷ (x ∷ σ)) (_ , fr< , nb) (zero ⦃ refl ⦄) = absurd (≤ᵣ-cons-neq fr<)
Partial-Halt (Op-ret ∷ ε) (fr< , nb) (more pf) = halt-cons Op-ret (Partial-Halt ε nb pf)
Partial-Halt (Op-ret ∷ (a ∷ σ)) (fr< , nb) (more pf) = halt-cons Op-ret (Partial-Halt (a ∷ σ) nb pf)
Partial-Halt (Op-var x ∷ σ) (fr< , nb) pf = halt-cons (Op-var x) (Partial-Halt σ nb pf)
Partial-Halt (Op-st x ∷ σ) (fr< , nb) pf = halt-cons (Op-st x) (Partial-Halt σ nb pf)
Partial-Halt (Op-lit n ∷ σ) (fr< , nb) pf = halt-cons (Op-lit n) (Partial-Halt σ nb pf)
Partial-Halt (Op-suc ∷ σ) (fr< , nb) pf = halt-cons Op-suc (Partial-Halt σ nb pf)
Partial-Halt (Op-recZ ∷ σ) (fr< , nb) pf = halt-cons Op-recZ (Partial-Halt σ nb (more pf))
Partial-Halt (Op-recS n ∷ σ) (fr< , nb) pf = halt-cons (Op-recS n) (Partial-Halt σ nb (more pf))
Partial-Halt (Op-add m n ∷ σ) (fr< , nb) pf = halt-cons (Op-add m n) (Partial-Halt σ nb pf)
Partial-Halt (Op-mult m n ∷ σ) (fr< , nb) pf = halt-cons (Op-mult m n) (Partial-Halt σ nb pf)
Partial-Halt (Op-pair ∷ σ) (fr< , nb) pf = halt-cons Op-pair (Partial-Halt σ nb pf)
Partial-Halt (Op-fst ∷ σ) (fr< , nb) pf = halt-cons Op-fst (Partial-Halt σ nb pf)
Partial-Halt (Op-snd ∷ σ) (fr< , nb) pf = halt-cons Op-snd (Partial-Halt σ nb pf)

Halt-F-Preservation : 
  (hf : Halt-F ⟨ ins , env , stack , fr ⟩) → 
  Γ ⊢ ins ∈ Δ ⟶ (Δ' ∷ A) → 
  env ⊨ Γ → 
  stack ⊨ Δ → 
  ⊢ (Halt-F.res hf) ∈ A
Halt-F-Preservation (halt-f σ nb ⦃ refl ⦄  ⦃ refl ⦄ ) ty-ins ty-env ty-st = 
  Preservation⇓ (Partial-Halt σ nb zero) (well-formed ty-ins ty-env ty-st Frame-nil)

-- 3. The biorthogonality construction
T↑ : (Val → Set) → Is × Env × Env × Frame → Set
T↑ P (ins , env , stack , fr) = ∀{v : Val} → P v → Halt-F ((ret , · ∷ v ) ⋈c (ins , env , stack , fr))

T↓ : (Is × Env × Env × Frame → Set) → Is × Env → Set
T↓ Q (ins , stack) = ∀{c} → Q c → Halt-F ((ins , stack) ⋈c c)

-- Halting set of values
Halt : (A : Ty) → (v : Val)  → Set
Halt-FC : Ty → Is → Env → Env → Frame → Set

Halt One <> = ⊤
Halt Nat (lit-n n) = ⊤
Halt (A ⇒ B) < env , ins > = 
  ⊢ < env , ins > ∈ (A ⇒ B) × (∀{v fr} → Halt A v → Halt-FC B ins (env ∷ v) · fr)
Halt (A ⊗ B) (v ,, v') = Halt A v × Halt B v'
Halt _ _ = ⊥

Halt-FC A ins env stack fr = Σ (Halt-F ⟨ ins , env , stack , fr ⟩) (λ hf → Halt A (Halt-F.res hf))

Halt-E : (Γ : Con) → Env → Set
Halt-E · · = ⊤
Halt-E · (env ∷ _) = ⊥
Halt-E (Γ ∷ A) · = ⊥
Halt-E (Γ ∷ A) (env ∷ v) = Halt-E Γ env × Halt A v

Halt-find-var : {x : Var Γ A} → Halt-E Γ env → [ x ↦ v ]∈ env → Halt A v
Halt-find-var {x = v₀} (henv , hv) hd = hv
Halt-find-var {x = vs x} (henv , hv) (tl pf) = Halt-find-var henv pf

Halt-ty : {v : Val} → Halt A v → ⊢ v ∈ A
Halt-ty {One} {<>} hv = Ty-unit
Halt-ty {A ⇒ B} {< env , ins >} (ty-clo , _) = ty-clo
Halt-ty {Nat} {lit-n n} hv = Ty-nat
Halt-ty {A ⊗ B} {v ,, v'} (hv , hv') = Ty-pair (Halt-ty hv) (Halt-ty hv')

Halt-split : ∀{Δ₁ Δ₂} → 
  Δ ≡ (Δ₁ ++ Δ₂) → 
  stack ⊨ Δ → 
  Halt-E Δ stack → 
  Σ Env (λ s1 → Σ Env (λ s2 → 
    stack ≡ (s1 ⋈e s2) × 
    s1 ⊨ Δ₁ × 
    s2 ⊨ Δ₂ ×
    Halt-E Δ₁ s1 ×
    Halt-E Δ₂ s2 ×
    len-E s2 ≡ len-C Δ₂
  ))
Halt-split {stack = stack} {Δ₂ = ·} refl ty-st hst = 
  stack , · , refl , ty-st , Env-nil , hst , tt , refl
Halt-split {stack = stack ∷ v} {Δ₂ = Δ₂ ∷ A} refl (Env-cons ta ty-st) (hst , ha) = 
  let 
    (s1 , s2 , eq' , ty-s1 , ty-s2 , h-s1 , h-s2 , eq) = Halt-split {stack = stack} {Δ₂ = Δ₂} refl ty-st hst 
  in 
    s1 , s2 ∷ v , cong (λ z → z ∷ v) eq' , ty-s1 , Env-cons ta ty-s2 , h-s1 , (h-s2 , ha) , cong suc eq


Halt-clo : 
  (Γ ∷ A) ⊢ ins ∈ · ⟶ (Δ ∷ B) → 
  env ⊨ Γ → 
  (∀{fr v} → Halt A v → Halt-FC B ins (env ∷ v) · fr) → 
  Halt (A ⇒ B) < env , ins > 
Halt-clo ty-ins ty-env asm = (Ty-clo ty-env ty-ins) , asm

funda :
  Γ ⊢ ins ∈ Δ ⟶ (Δ' ∷ A) → 
  env ⊨ Γ → 
  stack ⊨ Δ → 
  Halt-E Γ env → 
  Halt-E Δ stack →
  Halt-FC A ins env stack fr

funda-rec : 
  {inZ inS : Is}{fr : Frame} → 
  Γ ⊢ ins ∈ (Δ ∷ A) ⟶ (Δ' ∷ B) → 
  Γ ⊢ inZ ∈ · ⟶ (Γ' ∷ A) → 
  (Γ ∷ Nat ∷ A) ⊢ inS ∈ · ⟶ (Γ'' ∷ A) → 
  env ⊨ Γ → 
  stack ⊨ Δ →
  Halt-E Γ env → 
  Halt-E Δ stack →  
  (∀{v} → Halt A v → Σ (Halt-F ⟨ ins , env , stack ∷ v , fr ⟩) (λ hf → Halt B (Halt-F.res hf))) →
  (n : ℕ) → 
  Σ (Halt-F ⟨ rec inZ inS ⨾ ins , env , stack ∷ lit-n n , fr ⟩) (λ hf → Halt B (Halt-F.res hf))

funda Ty-ret ty-env (Env-cons ta ty-st) henv (hst , hv) = (halt-f ε zero) , hv

funda (Ty-⨾ Ty-pop ty-ins) ty-env (Env-cons ta ty-st) henv (hst , hv) 
  with funda ty-ins ty-env ty-st henv hst 
... | halt-f σ nb , hv = halt-f (Op-pop ∷ σ) (zero , nb) , hv

funda (Ty-⨾ Ty-swap ty-ins) ty-env (Env-cons tb (Env-cons ta ty-st)) henv ((hst , ha) , hb)
  with funda ty-ins ty-env (Env-cons ta (Env-cons tb ty-st)) henv ((hst , hb) , ha)
... | halt-f σ nb , hv = halt-f (Op-swap ∷ σ) (zero , nb) , hv

funda {fr = fr} (Ty-⨾ Ty-app ty-ins) ty-env (Env-cons ta (Env-cons (Ty-clo {ins = ins'} ty-env' ty-ins') ty-st)) henv ((hst , (ty-clo , hf)) , ha) = 
  let 
    asm = hf {fr = fr} ha 
    ind = funda ty-ins ty-env (Env-cons (Halt-F-Preservation (π₁ (hf ha)) ty-ins' (Env-cons ta ty-env') Env-nil) ty-st) henv (hst , π₂ (hf ha)) 
  in
  (halt-f 
    (Op-app ∷ (trace-rw (π₁ (hf ha)) ⋈ (Op-ret ∷ trace-rw (π₁ ind)))) 
    (zero , Not-below-⋈ {σ = trace-rw (π₁ (hf ha))} (Not-below-pred (nb-rw (π₁ (hf ha)))) ((more zero) , nb-rw (π₁ ind)))
  ) , 
  π₂ ind

funda (Ty-⨾ Ty-unit ty-ins) ty-env ty-st henv hst
  with funda ty-ins ty-env (Env-cons Ty-unit ty-st) henv (hst , tt)
... | halt-f σ nb , hv = halt-f (Op-unit ∷ σ) (zero , nb) , hv

funda (Ty-⨾ (Ty-var x) ty-ins) ty-env ty-st henv hst 
  with 
    (let ty-x = π₂ (find-var x ty-env) in 
    funda ty-ins ty-env (Env-cons (ty-[↦]∈ ty-env ty-x) ty-st) henv (hst , Halt-find-var henv ty-x))
... | halt-f σ nb , hv = halt-f (Op-var (π₂ (find-var x ty-env)) ∷ σ) (zero , nb) , hv

funda (Ty-⨾ (Ty-st x) ty-ins) ty-env ty-st henv hst
  with 
    (let ty-x = π₂ (find-var x ty-st) in 
    funda ty-ins ty-env (Env-cons (ty-[↦]∈ ty-st ty-x) ty-st) henv (hst , Halt-find-var hst ty-x))
... | halt-f σ nb , hv = halt-f (Op-st (π₂ (find-var x ty-st)) ∷ σ) (zero , nb) , hv

funda (Ty-⨾ (Ty-pushc ty-ins') ty-ins) ty-env ty-st henv hst
  with 
  funda ty-ins ty-env (Env-cons (Ty-clo ty-env ty-ins') ty-st) henv 
    (hst , Halt-clo ty-ins' ty-env λ hv → funda ty-ins' (Env-cons (Halt-ty hv) ty-env) Env-nil (henv , hv) tt)
... | halt-f σ nb , hv = halt-f (Op-pushc ∷ σ) (zero , nb) , hv

funda (Ty-⨾ (Ty-clo pfc refl ty-ins') ty-ins) ty-env ty-st henv hst 
  with Halt-split pfc ty-st hst
... | s1 , s2 , refl , ty-s1 , ty-s2 , h-s1 , h-s2 , eq
  with funda ty-ins ty-env (Env-cons (Ty-clo ty-s2 ty-ins') ty-s1) henv 
    (h-s1 , Halt-clo ty-ins' ty-s2 (λ hv → funda ty-ins' (Env-cons (Halt-ty hv) ty-s2) Env-nil (h-s2 , hv) tt))
... | halt-f σ nb , hv = halt-f (Op-clo refl eq ∷ σ) (zero , nb) , hv

funda (Ty-⨾ (Ty-lit n) ty-ins) ty-env ty-st henv hst 
  with funda ty-ins ty-env (Env-cons Ty-nat ty-st) henv (hst , tt)
... | halt-f σ nb , hv = halt-f (Op-lit n ∷ σ) (zero , nb) , hv

funda (Ty-⨾ Ty-suc ty-ins) ty-env (Env-cons Ty-nat ty-st) henv (hst , tt) 
  with funda ty-ins ty-env (Env-cons Ty-nat ty-st) henv (hst , tt)
... | halt-f σ nb , hv = halt-f (Op-suc ∷ σ) (zero , nb) , hv

funda (Ty-⨾ (Ty-rec tyZ tyS) ty-ins) ty-env (Env-cons (Ty-nat {n}) ty-st) henv (hst , tt) = 
  funda-rec ty-ins tyZ tyS ty-env ty-st henv hst (λ hv → funda ty-ins ty-env (Env-cons (Halt-ty hv) ty-st) henv (hst , hv)) n

funda (Ty-⨾ Ty-add ty-ins) ty-env (Env-cons (Ty-nat {n = n}) (Env-cons (Ty-nat {n = m}) ty-st)) henv ((hst , tt) , tt) 
  with funda ty-ins ty-env (Env-cons Ty-nat ty-st) henv (hst , tt) 
... | halt-f σ nb , hv = halt-f (Op-add m n ∷ σ) (zero , nb) , hv 

funda (Ty-⨾ Ty-mult ty-ins) ty-env (Env-cons (Ty-nat {n = n}) (Env-cons (Ty-nat {n = m}) ty-st)) henv ((hst , tt) , tt)
  with funda ty-ins ty-env (Env-cons Ty-nat ty-st) henv (hst , tt) 
... | halt-f σ nb , hv = halt-f (Op-mult m n ∷ σ) (zero , nb) , hv

funda (Ty-⨾ Ty-pair ty-ins) ty-env (Env-cons tb (Env-cons ta ty-st)) henv ((hst , ha) , hb) 
  with funda ty-ins ty-env (Env-cons (Ty-pair ta tb) ty-st) henv (hst , (ha , hb)) 
... | halt-f σ nb , hv = halt-f (Op-pair ∷ σ) (zero , nb) , hv

funda (Ty-⨾ Ty-fst ty-ins) ty-env (Env-cons (Ty-pair ta tb) ty-st) henv (hst , (ha , hb))   
  with funda ty-ins ty-env (Env-cons ta ty-st) henv (hst , ha) 
... | halt-f σ nb , hv = halt-f (Op-fst ∷ σ) (zero , nb) , hv

funda (Ty-⨾ Ty-snd ty-ins) ty-env (Env-cons (Ty-pair ta tb) ty-st) henv (hst , (ha , hb))   
  with funda ty-ins ty-env (Env-cons tb ty-st) henv (hst , hb) 
... | halt-f σ nb , hv = halt-f (Op-snd ∷ σ) (zero , nb) , hv

funda-rec ty-ins tyZ tyS ty-env ty-st henv hst asm zero = 
  let 
    indZ = funda tyZ ty-env Env-nil henv tt 
  in
  (halt-f (Op-recZ ∷ (trace-rw (π₁ indZ) ⋈ (Op-ret ∷ trace-rw (π₁ (asm (π₂ indZ)))))) 
  (zero , Not-below-⋈ {σ = trace-rw (π₁ indZ)} (Not-below-pred (nb-rw (π₁ indZ))) (more zero , nb-rw (π₁ (asm (π₂ indZ)))))) , 
  π₂ (asm (π₂ indZ))

funda-rec {ins = ins} {A = A} {env = env} {stack = stack} {inZ = inZ} {inS = inS} {fr = fr} 
  ty-ins tyZ tyS ty-env ty-st henv hst asm (suc n) = 
  halt-f (Op-recS n ∷ (trace-rw (π₁ ind) ⋈ (Op-ret ∷ trace-rw (π₁ (asm (π₂ ind)))))) 
    (zero , Not-below-⋈ {σ = trace-rw (π₁ ind)} (Not-below-pred (nb-rw (π₁ ind))) ((more zero) , nb-rw (π₁ (asm (π₂ ind))))) , 
  π₂ (asm (π₂ ind))
  where
    h-cloS : ∀{n} → Halt (A ⇒ A) (< env ∷ lit-n n , inS >)
    h-cloS = (Ty-clo (Env-cons Ty-nat ty-env) tyS) , λ hv → funda tyS (Env-cons (Halt-ty hv) (Env-cons Ty-nat ty-env)) Env-nil ((henv , tt) , hv) tt
    
    ind : ∀{fr} → Σ (Halt-F ⟨ rec inZ inS ⨾ app ⨾ ret , env , · ∷ < env ∷ lit-n n , inS > ∷ lit-n n , fr ⟩) (λ hf → Halt A (Halt-F.res hf)) 
    ind = funda-rec (Ty-⨾ Ty-app Ty-ret) tyZ tyS ty-env (Env-cons (Ty-clo (Env-cons Ty-nat ty-env) tyS) Env-nil) henv 
      (tt , (Ty-clo (Env-cons Ty-nat ty-env) tyS) , λ hv → (π₂ h-cloS) hv) 
      (λ hv → 
        halt-f (Op-app ∷ (trace-rw (π₁ ((π₂ h-cloS) hv)) ⋈ (Op-ret ∷ ε))) 
        (zero , Not-below-⋈ {σ = trace-rw (π₁ ((π₂ h-cloS) hv))} (Not-below-pred (nb-rw (π₁ ((π₂ h-cloS) hv)))) (more zero , zero)) , 
        π₂ ((π₂ h-cloS) hv)) 
      n

-- Termination, by the fundamental lemma.
-- Every well-typed value is in halt.
mutual
  Halting : ⊢ v ∈ A → Halt A v
  Halting Ty-unit = tt
  Halting {A = A ⇒ B} (Ty-clo {env = env} {ins = ins} ty-env ty-ins) = 
    let henv = Halting-E ty-env in 
      Ty-clo ty-env ty-ins , λ hv → funda ty-ins (Env-cons (Halt-ty hv) ty-env) Env-nil (henv , hv) tt
  Halting Ty-nat = tt
  Halting (Ty-pair ta tb) = Halting ta , Halting tb

  Halting-E : env ⊨ Γ → Halt-E Γ env
  Halting-E Env-nil = tt
  Halting-E (Env-cons ta ty-env) = Halting-E ty-env , Halting ta

-- Well-formed configurations halt at the current frame.
Termination-F : WF-Config A₀ c → Halt-F c
Termination-F (well-formed ty-ins ty-env ty-st ty-fr) = 
  π₁ (funda ty-ins ty-env ty-st (Halting-E ty-env) (Halting-E ty-st))

-- Well-formed configurations halt, by induction on the number of frames.
Termination : WF-Config A₀ c → (Σ Val (λ v → c ⇓ v))
Termination (well-formed ty-ins ty-env ty-st ty-fr) = lem ty-ins ty-env ty-st ty-fr
  where
    lem : 
      Γ ⊢ ins ∈ Δ ⟶ (Δ' ∷ A) →
      env ⊨ Γ → 
      stack ⊨ Δ →
      Γ' ⊢ᵣ fr ∈ A ⟶ A₀ → 
      (Σ Val (λ v → ⟨ ins , env , stack , fr ⟩ ⇓ v))
    lem ty-ins ty-env ty-st Frame-nil with Termination-F (well-formed ty-ins ty-env ty-st Frame-nil)
    ... | halt-f {res = v} σ nb ⦃ refl ⦄ ⦃ refl ⦄ = v , halt σ
    lem ty-ins ty-env ty-st (Frame-cons ty-fr ty-ins' ty-env' ty-st')
      with Termination-F (well-formed ty-ins ty-env ty-st (Frame-cons ty-fr ty-ins' ty-env' ty-st'))
    ... | halt-f σ nb ⦃ refl ⦄ ⦃ refl ⦄ with lem ty-ins' ty-env' (Env-cons (Halt-F-Preservation (halt-f σ nb) ty-ins ty-env ty-st) ty-st') ty-fr
    ... | v , halt σ' =  v , (halt (σ ⋈ (Op-ret ∷ σ')))

-- Using the termination proof as an evaluator
eval : WF-Config A₀ c → Val
eval wf = π₁ (Termination wf)

exec : · ⊢ ins ∈ · ⟶ (Δ ∷ A) → (Σ Val (λ v → ⟨ ins , · , · , · ⟩ ⇓ v))
exec ty-ins = Termination (well-formed ty-ins Env-nil Env-nil Frame-nil)

-- Prototype of a more practical evaluator: 
-- steps the machine using the type-safety theorem, and guarantees 
-- termination with the termination proof.
-- The typing judgement and the termination proof can be erased at runtime.

Termination-n : WF-Config A₀ c → Σ Val (λ v → Σ ℕ (λ n → c ⇓₀ v , n))
Termination-n wf with Termination wf
... | v , halt σ = v , (⇓-count σ)

eval' : WF-Config A₀ c → Val
eval' {c = c} wf = eval-aux c wf (π₂ (π₂ (Termination-n wf)))
  where 
    eval-aux : 
      {n : ℕ} → (c : Config) → WF-Config A₀ c → (c ⇓₀ v , n) → Val
    eval-aux {n = zero} (⟨ ret , env , stack ∷ v , · ⟩) wf finish = v
    eval-aux {n = suc n} c wf (step σ op) with Progress wf
    eval-aux {v = _} {suc n} c wf (step σ ()) | inj₁ (_ , finish)
    ... | inj₂ (c' , op') rewrite Determinacy op op' = eval-aux c' (Preservation op' wf) σ

Termination-n+ : 
    {i : Instr} → 
    Γ ⊢ᵢ i ∈ Δ'' ⟶ Δ →  
    Γ ⊢ ins ∈ Δ ⟶ (Δ' ∷ A) →
    env ⊨ Γ → 
    stack ⊨ Δ'' →
    Γ' ⊢ᵣ fr ∈ A ⟶ A₀ → 
    Σ Val (λ v → Σ ℕ (λ n → ⟨ (i ⨾ ins) , env , stack , fr ⟩ ⇓₀ v , suc n))
Termination-n+ ty-i ty-ins ty-env ty-stack ty-fr 
  with Progress (well-formed (Ty-⨾ ty-i ty-ins) ty-env ty-stack ty-fr)
... | inj₂ (c , op) = 
  let v , n' , tr = Termination-n (Preservation op (well-formed (Ty-⨾ ty-i ty-ins) ty-env ty-stack ty-fr)) in
    v , n' , step tr op


