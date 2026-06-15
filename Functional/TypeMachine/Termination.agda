module Functional.TypeMachine.Termination where 

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
Halt One <> = ⊤
Halt Nat (lit-n n) = ⊤
Halt (A ⇒ B) < env , ins > = 
  ⊢ < env , ins > ∈ (A ⇒ B) ×   -- the closure is well-typed, and
  (∀{v} → Halt A v →              -- for all values v in Halt A: 
    -- 1. applying the closure to v halts in every evaluation context
    T↓ (T↑ (Halt B)) ((app ⨾ ret) , (· ∷ < env , ins > ∷ v)) ×
    -- 2. if the closure's code halts, its result is in Halt B
    ({fr : Frame} → (hf : Halt-F ⟨ ins , (env ∷ v) , · , fr ⟩) → Halt B (Halt-F.res hf)))
Halt (A ⊗ B) (v ,, v') = Halt A v × Halt B v'
Halt _ _ = ⊥

Halt-E : (Γ : Con) → Env → Set
Halt-E · · = ⊤
Halt-E · (env ∷ _) = ⊥
Halt-E (Γ ∷ A) · = ⊥
Halt-E (Γ ∷ A) (env ∷ v) = Halt-E Γ env × Halt A v

Halt-find-var : {x : Var Γ A} → Halt-E Γ env → [ x ↦ v ]∈ env → Halt A v
Halt-find-var {x = v₀} (h-env , hv) hd = hv
Halt-find-var {x = vs x} (h-env , hv) (tl pf) = Halt-find-var h-env pf

Halt-ty : {v : Val} → Halt A v → ⊢ v ∈ A
Halt-ty {One} {<>} hv = Ty-unit
Halt-ty {A ⇒ B} {< env , ins >} (ty-clo , _) = ty-clo
Halt-ty {Nat} {lit-n n} hv = Ty-nat
Halt-ty {A ⊗ B} {v ,, v'} (hv , hv') = Ty-pair (Halt-ty hv) (Halt-ty hv')

-- Helper function for showing a closure is in halt, given the fundamental lemma.
Halt-clo : 
  (Γ ∷ A) ⊢ ins ∈ · ⟶ (Δ ∷ B) → 
  env ⊨ Γ → 
  (∀{fr v} → Halt A v → Halt-F ⟨ ins , env ∷ v , · , fr ⟩) → 
  (∀{fr v} → Halt A v → (hf : Halt-F ⟨ ins , env ∷ v , · , fr ⟩) → Halt B (Halt-F.res hf)) →
  Halt (A ⇒ B) < env , ins > 
Halt-clo ty-env ty-ins ind1 ind2 = 
  Ty-clo ty-ins ty-env , 
  λ ha → 
    (λ asm → 
      let h1 = ind1 ha in
      let h2 = ind2 ha h1 in
      halt-f 
        (Op-app ∷ (trace-rw h1 ⋈ (Op-ret ∷ trace-rw (asm h2)))) 
        (zero , (Not-below-⋈ {σ = trace-rw (ind1 ha)} (Not-below-pred (nb-rw h1)) ((more zero) , nb-rw (asm h2))))
      ) , 
    (λ hf → ind2 ha hf)

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
Halt-split {stack = stack} {Δ₂ = ·} refl ty-st h-st = 
  stack , · , refl , ty-st , Env-nil , h-st , tt , refl
Halt-split {stack = stack ∷ v} {Δ₂ = Δ₂ ∷ A} refl (Env-cons ta ty-st) (h-st , ha)
 with Halt-split {stack = stack} {Δ₂ = Δ₂} refl ty-st h-st 
... | s1 , s2 , refl , ty-s1 , ty-s2 , h-s1 , h-s2 , eq = 
  s1 , s2 ∷ v , refl , ty-s1 , Env-cons ta ty-s2 , h-s1 , (h-s2 , ha) , cong suc eq

Halt-split-ty : 
  ∀{Δ₁ Δ₂ s1 s2} → 
  stack ⊨ Δ →
  Δ ≡ (Δ₁ ++ Δ₂) →  
  stack ≡ (s1 ⋈e s2) → 
  len-C Δ₂ ≡ len-E s2 → 
  Halt-E Δ stack → 
  s1 ⊨ Δ₁ × s2 ⊨ Δ₂ × Halt-E Δ₁ s1 × Halt-E Δ₂ s2
Halt-split-ty {Δ₂ = ·} {s2 = ·} ty-st refl refl refl h-st = 
  ty-st , Env-nil , h-st , tt
Halt-split-ty {Δ₂ = Δ₂ ∷ A} {s2 = s2 ∷ v} (Env-cons ta ty-st) refl refl eq-len (h-st , ha) 
  with Halt-split-ty ty-st refl refl (suc-inj eq-len) h-st
... | ty-s1 , ty-s2 , h-s1 , h-s2 = 
  ty-s1 , Env-cons ta ty-s2 , h-s1 , (h-s2 , ha)

{- 
  The fundamental lemma states that:
    well-typed machine with halting environment and stack halts at the current frame
    and the resulting value is also in halt.

  Implementation-wise, it is split into four mutual recursive definitions.
    funda: the machine halts.
    funda2: if the machine halts, then the resulting value is in halt.
  It's easier to prove this way, since Agda can't keep track of some definitional equalities
  of the traces.
    funda-rec, funda2-rec: lemmas for the recursor case, doing induction over n : ℕ.
-} 

funda :
  Γ ⊢ ins ∈ Δ ⟶ (Δ' ∷ A) → 
  env ⊨ Γ → 
  stack ⊨ Δ → 
  Halt-E Γ env → 
  Halt-E Δ stack →
  Halt-F ⟨ ins , env , stack , fr ⟩

funda2 : 
  Γ ⊢ ins ∈ Δ ⟶ (Δ' ∷ A) → 
  env ⊨ Γ → 
  stack ⊨ Δ → 
  Halt-E Γ env → 
  Halt-E Δ stack →
  (hf : Halt-F ⟨ ins , env , stack , fr ⟩) → 
  Halt A (Halt-F.res hf)

funda-rec : 
  {inZ inS : Is}{fr : Frame} → 
  Γ ⊢ ins ∈ (Δ ∷ A) ⟶ (Δ' ∷ B) → 
  Γ ⊢ inZ ∈ · ⟶ (Γ' ∷ A) → 
  (Γ ∷ Nat ∷ A) ⊢ inS ∈ · ⟶ (Γ'' ∷ A) → 
  env ⊨ Γ → 
  stack ⊨ Δ →
  Halt-E Γ env → 
  Halt-E Δ stack →  
  (∀{v} → Halt A v → Halt-F ⟨ ins , env , stack ∷ v , fr ⟩) →
  (n : ℕ) → 
  Halt-F ⟨ rec inZ inS ⨾ ins , env , stack ∷ lit-n n , fr ⟩

funda2-rec : 
  {inZ inS : Is}{fr : Frame} → 
  Γ ⊢ ins ∈ (Δ ∷ A) ⟶ (Δ' ∷ B) → 
  Γ ⊢ inZ ∈ · ⟶ (Γ' ∷ A) → 
  (Γ ∷ Nat ∷ A) ⊢ inS ∈ · ⟶ (Γ'' ∷ A) → 
  env ⊨ Γ → 
  stack ⊨ Δ →
  Halt-E Γ env → 
  Halt-E Δ stack →  
  (∀{v} → Halt A v → (hf : Halt-F ⟨ ins , env , stack ∷ v , fr ⟩) → Halt B (Halt-F.res hf)) →
  (n : ℕ) → 
  (hf : Halt-F ⟨ rec inZ inS ⨾ ins , env , stack ∷ lit-n n , fr ⟩) → 
  Halt B (Halt-F.res hf)

funda Ty-ret ty-env (Env-cons ta ty-st) h-env (h-st , hv) = halt-f ε zero

funda (Ty-⨾ Ty-pop ty-ins) ty-env (Env-cons _ ty-st) h-env (h-st , _)
  with funda ty-ins ty-env ty-st h-env h-st
... | halt-f σ nb = halt-f (Op-pop ∷ σ) (zero , nb)

funda (Ty-⨾ Ty-swap ty-ins) ty-env (Env-cons tb (Env-cons ta ty-st)) h-env ((h-st , ha) , hb)
  with funda ty-ins ty-env (Env-cons ta (Env-cons tb ty-st)) h-env ((h-st , hb) , ha)
... | halt-f σ nb = halt-f (Op-swap ∷ σ) (zero , nb)

-- Application halts by the logical relation's definition.
funda {fr = fr} (Ty-⨾ Ty-app ty-ins) ty-env (Env-cons ta (Env-cons (Ty-clo {ins = ins'} ty-env' ty-ins') ty-st)) h-env ((h-st , (ty-clo , hf)) , ha) with hf ha 
... | halt-TT , halt-B = halt-TT (λ hb → funda {fr = fr} ty-ins ty-env (Env-cons (Halt-ty hb) ty-st) h-env (h-st , hb))

funda (Ty-⨾ Ty-unit ty-ins) ty-env ty-st h-env h-st
  with funda ty-ins ty-env (Env-cons Ty-unit ty-st) h-env (h-st , tt)
... | halt-f σ nb = halt-f (Op-unit ∷ σ) (zero , nb)

funda (Ty-⨾ (Ty-var x) ty-ins) ty-env ty-st h-env h-st 
  with 
    (let ty-x = π₂ (find-var x ty-env) in 
    funda ty-ins ty-env (Env-cons (ty-[↦]∈ ty-env ty-x) ty-st) h-env (h-st , Halt-find-var h-env ty-x))
... | halt-f σ nb = halt-f (Op-var (π₂ (find-var x ty-env)) ∷ σ) (zero , nb)

funda (Ty-⨾ (Ty-st x) ty-ins) ty-env ty-st h-env h-st
  with 
    (let ty-x = π₂ (find-var x ty-st) in 
    funda ty-ins ty-env (Env-cons (ty-[↦]∈ ty-st ty-x) ty-st) h-env (h-st , Halt-find-var h-st ty-x))
... | halt-f σ nb = halt-f (Op-st (π₂ (find-var x ty-st)) ∷ σ) (zero , nb)

-- Goal: the closure just pushed is in halt. See Halt-clo.
funda {fr = fr} (Ty-⨾ (Ty-pushc ty-ins') ty-ins) ty-env ty-st h-env h-st with 
    funda {fr = fr} ty-ins ty-env (Env-cons (Ty-clo ty-env ty-ins') ty-st) h-env (h-st , 
      Halt-clo ty-ins' ty-env 
        (λ ha → funda ty-ins' (Env-cons (Halt-ty ha) ty-env) Env-nil (h-env , ha) tt ) 
        (λ ha hf → funda2 ty-ins' (Env-cons (Halt-ty ha) ty-env) Env-nil (h-env , ha) tt hf ) )
... | halt-f σ nb = halt-f (Op-pushc ∷ σ) (zero , nb)

-- Similar to push-c, but more tedious due to stack-partition operations.
funda {fr = fr} (Ty-⨾ (Ty-clo pf-c len< ty-ins') ty-ins) ty-env ty-st h-env h-st 
  with Halt-split pf-c ty-st h-st
... | s1 , s2 , refl , ty-s1 , ty-s2 , h-s1 , h-s2 , eq 
  with 
    funda {fr = fr} ty-ins ty-env (Env-cons (Ty-clo ty-s2 ty-ins') ty-s1) h-env 
      (h-s1 , 
        Halt-clo ty-ins' ty-s2 
          (λ ha → funda ty-ins' (Env-cons (Halt-ty ha) ty-s2) Env-nil (h-s2 , ha) tt )
          λ ha hf → funda2 ty-ins' (Env-cons (Halt-ty ha) ty-s2) Env-nil (h-s2 , ha) tt hf
      )
... | halt-f σ nb = halt-f ((Op-clo refl (trans eq len<)) ∷ σ) (zero , nb)

funda (Ty-⨾ (Ty-lit n) ty-ins) ty-env ty-st h-env h-st 
  with funda ty-ins ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt)
... | halt-f σ nb = halt-f (Op-lit n ∷ σ) (zero , nb)

funda (Ty-⨾ Ty-suc ty-ins) ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt) 
  with funda ty-ins ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt)
... | halt-f σ nb = halt-f (Op-suc ∷ σ) (zero , nb)

funda 
  {Γ = Γ} {ins = rec inZ inS ⨾ ins} {env = env} {stack = stack ∷ lit-n n} {fr = fr} 
  (Ty-⨾ (Ty-rec {A = A} tyZ tyS) ty-ins) ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt) = 
    funda-rec ty-ins tyZ tyS ty-env ty-st h-env h-st ind n 
  where
    ind : Halt A v → Halt-F ⟨ ins , env , stack ∷ v , fr ⟩
    ind hv = funda ty-ins ty-env (Env-cons (Halt-ty hv) ty-st) h-env (h-st , hv)

funda (Ty-⨾ Ty-add ty-ins) ty-env (Env-cons (Ty-nat {n = n}) (Env-cons (Ty-nat {n = m}) ty-st)) h-env ((h-st , tt) , tt) 
  with funda ty-ins ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt) 
... | halt-f σ nb = halt-f (Op-add m n ∷ σ) (zero , nb)

funda (Ty-⨾ Ty-mult ty-ins) ty-env (Env-cons (Ty-nat {n = n}) (Env-cons (Ty-nat {n = m}) ty-st)) h-env ((h-st , tt) , tt)
  with funda ty-ins ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt) 
... | halt-f σ nb = halt-f (Op-mult m n ∷ σ) (zero , nb)

funda (Ty-⨾ Ty-pair ty-ins) ty-env (Env-cons tb (Env-cons ta ty-st)) h-env ((h-st , ha) , hb) 
  with funda ty-ins ty-env (Env-cons (Ty-pair ta tb) ty-st) h-env (h-st , (ha , hb)) 
... | halt-f σ nb = halt-f (Op-pair ∷ σ) (zero , nb)

funda (Ty-⨾ Ty-fst ty-ins) ty-env (Env-cons (Ty-pair ta tb) ty-st) h-env (h-st , (ha , hb))   
  with funda ty-ins ty-env (Env-cons ta ty-st) h-env (h-st , ha) 
... | halt-f σ nb = halt-f (Op-fst ∷ σ) (zero , nb)

funda (Ty-⨾ Ty-snd ty-ins) ty-env (Env-cons (Ty-pair ta tb) ty-st) h-env (h-st , (ha , hb))   
  with funda ty-ins ty-env (Env-cons tb ty-st) h-env (h-st , hb) 
... | halt-f σ nb = halt-f (Op-snd ∷ σ) (zero , nb)

funda2 {fr = fr} Ty-ret ty-env (Env-cons ta ty-st) h-env (h-st , hv) (halt-f ε nb) = hv

funda2 {fr = fr} Ty-ret ty-env (Env-cons ta ty-st) h-env (h-st , hv) (halt-f (Op-ret ∷ (_ ∷ σ)) (_ , fr< , nb)) = absurd (≤ᵣ-cons-neq fr<)

funda2 (Ty-⨾ Ty-pop ty-ins) ty-env (Env-cons _ ty-st) h-env (h-st , _) (halt-f (Op-pop ∷ σ) (fr< , nb)) =
  funda2 ty-ins ty-env ty-st h-env h-st (halt-f σ nb)

funda2 (Ty-⨾ Ty-swap ty-ins) ty-env (Env-cons tb (Env-cons ta ty-st)) h-env ((h-st , ha) , hb) (halt-f (Op-swap ∷ σ) (fr< , nb)) =
  funda2 ty-ins ty-env (Env-cons ta (Env-cons tb ty-st)) h-env ((h-st , hb) , ha) (halt-f σ nb)

-- Need the apply-split lemma to break down the halting sequence, and use I.H. 
-- to show that the value returned from this application is in halt.
funda2 {fr = fr} (Ty-⨾ Ty-app ty-ins) ty-env (Env-cons ta (Env-cons (Ty-clo {ins = ins'} ty-env' ty-ins') ty-st)) h-env ((h-st , ty-clo , hf) , ha) (halt-f (Op-app ∷ σ) (fr< , nb) ⦃ refl ⦄ ⦃ refl ⦄) 
  with Apply-split σ | hf ha
... | dump' , res' , σ₁ , σ₂ , eq , nb1 | halt-TT , halt-B = 
  let nbs = Not-below-⋈-inv {σ₁ = σ₁} {σ₂ = Op-ret ∷ σ₂} nb eq in
  let hf₁ = halt-f σ₁ nb1 in
  funda2 ty-ins ty-env (Env-cons (Halt-F-Preservation hf₁ ty-ins' (Env-cons ta ty-env') Env-nil) ty-st) h-env (h-st , halt-B hf₁) (halt-f σ₂ (π₂ (π₂ nbs)))

funda2 (Ty-⨾ Ty-unit ty-ins) ty-env ty-st h-env h-st (halt-f (Op-unit ∷ σ) (fr< , nb)) = 
  funda2 ty-ins ty-env (Env-cons Ty-unit ty-st) h-env (h-st , tt) (halt-f σ nb)

funda2 (Ty-⨾ (Ty-var x) ty-ins) ty-env ty-st h-env h-st (halt-f (Op-var ty-x ∷ σ) (fr< , nb)) = 
  funda2 ty-ins ty-env (Env-cons (ty-[↦]∈ ty-env ty-x) ty-st) h-env (h-st , Halt-find-var h-env ty-x) (halt-f σ nb)

funda2 (Ty-⨾ (Ty-st x) ty-ins) ty-env ty-st h-env h-st (halt-f (Op-st ty-x ∷ σ) (fr< , nb)) =
  funda2 ty-ins ty-env (Env-cons (ty-[↦]∈ ty-st ty-x) ty-st) h-env (h-st , Halt-find-var h-st ty-x) (halt-f σ nb)

funda2 (Ty-⨾ (Ty-pushc ty-ins') ty-ins) ty-env ty-st h-env h-st (halt-f (Op-pushc ∷ σ) (fr< , nb)) =  
  funda2 ty-ins ty-env (Env-cons (Ty-clo ty-env ty-ins') ty-st) h-env (h-st , 
    Halt-clo ty-ins' ty-env 
      (λ ha → funda ty-ins' (Env-cons (Halt-ty ha) ty-env) Env-nil (h-env , ha) tt ) 
      (λ ha hf → funda2 ty-ins' (Env-cons (Halt-ty ha) ty-env) Env-nil (h-env , ha) tt hf ) )
  (halt-f σ nb)

funda2 (Ty-⨾ (Ty-clo pf-c len<-c ty-ins') ty-ins) ty-env ty-st h-env h-st (halt-f ((Op-clo {s1 = s1} {s2 = s2} pf len<) ∷ σ) (fr< , nb))  
  with Halt-split-ty ty-st pf-c pf (trans len<-c (sym len<)) h-st  
... | ty-s1 , ty-s2 , h-s1 , h-s2 = 
  funda2 ty-ins ty-env (Env-cons (Ty-clo ty-s2 ty-ins') ty-s1) h-env (h-s1 , 
    Halt-clo ty-ins' ty-s2 
        (λ ha → funda ty-ins' (Env-cons (Halt-ty ha) ty-s2) Env-nil (h-s2 , ha) tt ) 
        (λ ha hf → funda2 ty-ins' (Env-cons (Halt-ty ha) ty-s2) Env-nil (h-s2 , ha) tt hf ) 
    ) 
  (halt-f σ nb)

funda2 (Ty-⨾ (Ty-lit n) ty-ins) ty-env ty-st h-env h-st (halt-f (Op-lit n ∷ σ) (fr< , nb)) = 
  funda2 ty-ins ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt) (halt-f σ nb)

funda2 (Ty-⨾ Ty-suc ty-ins) ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt) (halt-f (Op-suc ∷ σ) (fr< , nb)) = 
  funda2 ty-ins ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt) (halt-f σ nb) 
funda2 
  {Γ = Γ} {ins = rec inZ inS ⨾ ins} {A = B} {env = env} {stack = stack ∷ lit-n n} {fr = fr} 
  (Ty-⨾ (Ty-rec {A = A} tyZ tyS) ty-ins) ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt) hf = 
    funda2-rec ty-ins tyZ tyS ty-env ty-st h-env h-st ind2 n hf
  where
    ind : Halt A v → Halt-F ⟨ ins , env , stack ∷ v , fr ⟩
    ind hv = funda ty-ins ty-env (Env-cons (Halt-ty hv) ty-st) h-env (h-st , hv)

    ind2 : Halt A v → (hf : Halt-F ⟨ ins , env , stack ∷ v , fr ⟩) → Halt B (Halt-F.res hf)
    ind2 hv hf = funda2 ty-ins ty-env (Env-cons (Halt-ty hv) ty-st) h-env (h-st , hv) hf

    ind-Z : ∀{fr} → Halt-F ⟨ inZ , env , · , fr ⟩
    ind-Z = funda tyZ ty-env Env-nil h-env tt

    ind2-Z : ∀{fr} → (hf : Halt-F ⟨ inZ , env , · , fr ⟩) → Halt _ (Halt-F.res hf)
    ind2-Z hf = funda2 tyZ ty-env Env-nil h-env tt hf
    
    h-cloS : ∀{n} → Halt (A ⇒ A) (< env ∷ lit-n n , inS >)
    h-cloS = 
      Halt-clo tyS (Env-cons Ty-nat ty-env) 
        (λ ha → funda tyS (Env-cons (Halt-ty ha) (Env-cons Ty-nat ty-env)) Env-nil ((h-env , tt) , ha) tt ) 
        (λ ha hf → funda2 tyS (Env-cons (Halt-ty ha) (Env-cons Ty-nat ty-env)) Env-nil ((h-env , tt) , ha) tt hf )

funda2 (Ty-⨾ Ty-add ty-ins) ty-env (Env-cons Ty-nat (Env-cons Ty-nat ty-st)) h-env ((h-st , tt) , tt) (halt-f (Op-add m n ∷ σ) (fr< , nb)) = 
  funda2 ty-ins ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt) (halt-f σ nb)

funda2 (Ty-⨾ Ty-mult ty-ins) ty-env (Env-cons Ty-nat (Env-cons Ty-nat ty-st)) h-env ((h-st , tt) , tt) (halt-f (Op-mult m n ∷ σ) (fr< , nb)) = 
  funda2 ty-ins ty-env (Env-cons Ty-nat ty-st) h-env (h-st , tt) (halt-f σ nb)

funda2 (Ty-⨾ Ty-pair ty-ins) ty-env (Env-cons tb (Env-cons ta ty-st)) h-env ((h-st , ha) , hb) (halt-f (Op-pair ∷ σ) (fr< , nb)) = 
  funda2 ty-ins ty-env (Env-cons (Ty-pair ta tb) ty-st) h-env (h-st , ha , hb) (halt-f σ nb)

funda2 (Ty-⨾ Ty-fst ty-ins) ty-env (Env-cons (Ty-pair ta tb) ty-st) h-env (h-st , (ha , hb))  (halt-f (Op-fst ∷ σ) (fr< , nb)) =
  funda2 ty-ins ty-env (Env-cons ta ty-st) h-env (h-st , ha) (halt-f σ nb)

funda2 (Ty-⨾ Ty-snd ty-ins) ty-env (Env-cons (Ty-pair ta tb) ty-st) h-env (h-st , (ha , hb)) (halt-f (Op-snd ∷ σ) (fr< , nb)) = 
  funda2 ty-ins ty-env (Env-cons tb ty-st) h-env (h-st , hb) (halt-f σ nb)

funda-rec ty-ins tyZ tyS ty-env ty-st h-env h-st asm zero = 
  let ind-Z = funda tyZ ty-env Env-nil h-env tt in
  let ind-asm = asm (funda2 tyZ ty-env Env-nil h-env tt ind-Z) in
  halt-f 
    (Op-recZ ∷ (trace-rw ind-Z ⋈ (Op-ret ∷ trace-rw ind-asm ))) 
    (zero , Not-below-⋈ {σ = trace-rw ind-Z} (Not-below-pred (nb-rw ind-Z)) (more zero , nb-rw ind-asm))

funda-rec {ins = ins} {A = A} {env = env} {stack = stack} {inZ = inZ} {inS = inS} {fr = fr} ty-ins tyZ tyS ty-env ty-st h-env h-st asm (suc n) = 
  halt-f 
    (Op-recS n ∷ ((trace-rw ind) ⋈ (Op-ret ∷ trace-rw (asm ind2))))
    (zero , (Not-below-⋈ {σ = trace-rw ind} (Not-below-pred (nb-rw ind)) (more zero , nb-rw (asm ind2))))
  where 
    h-cloS : ∀{n} → Halt (A ⇒ A) (< env ∷ lit-n n , inS >)
    h-cloS = 
      Halt-clo tyS (Env-cons Ty-nat ty-env) 
        (λ ha → funda tyS (Env-cons (Halt-ty ha) (Env-cons Ty-nat ty-env)) Env-nil ((h-env , tt) , ha) tt ) 
        (λ ha hf → funda2 tyS (Env-cons (Halt-ty ha) (Env-cons Ty-nat ty-env)) Env-nil ((h-env , tt) , ha) tt hf )
 
    asm' : ∀{n v fr} → Halt A v → Halt-F ⟨ app ⨾ ret , env , · ∷ < env ∷ lit-n n , inS > ∷ v , fr ⟩
    asm' hv = π₁ ((π₂ h-cloS) hv) (λ _ → halt-f ε zero) 

    asm2' : ∀{n v fr} → Halt A v → (hf : Halt-F ⟨ app ⨾ ret , env , · ∷ < env ∷ lit-n n , inS > ∷ v , fr ⟩) → Halt A (Halt-F.res hf)
    asm2' hv (halt-f (Op-app ∷ σ) (_ , nb) ⦃ refl ⦄ ⦃ refl ⦄) with Apply-split σ
    ... | _ , res , σ₁ , σ₂ , refl , nb' =
      let nb2 = π₂ (π₂ (Not-below-⋈-inv {σ₁ = σ₁} nb refl)) in
      let eq = π₂ (∷-inj (Not-below-ret σ₂ refl nb2)) in 
      subst (Halt A) eq (π₂ (π₂ h-cloS hv) (halt-f σ₁ nb'))

    ind : ∀{fr} → Halt-F ⟨ rec inZ inS ⨾ app ⨾ ret , env , · ∷ < env ∷ lit-n n , inS > ∷ lit-n n , fr ⟩ 
    ind = funda-rec (Ty-⨾ Ty-app Ty-ret) tyZ tyS ty-env (Env-cons (Ty-clo (Env-cons Ty-nat ty-env) tyS) Env-nil) h-env (tt , h-cloS) asm' n

    ind2 = funda2-rec (Ty-⨾ Ty-app Ty-ret) tyZ tyS ty-env (Env-cons (Ty-clo (Env-cons Ty-nat ty-env) tyS) Env-nil) h-env (tt , h-cloS) asm2' n ind

funda2-rec ty-ins tyZ tyS ty-env ty-st h-env h-st asm zero (halt-f (Op-recZ ∷ σ) (_ , nb) ⦃ refl ⦄ ⦃ refl ⦄) 
  with Apply-split σ
... | dump , res , δ₁ , δ₂ , refl , nb1 = 
  let nbs = Not-below-⋈-inv {σ₁ = δ₁} nb refl in
  asm (funda2 tyZ ty-env Env-nil h-env tt (halt-f δ₁ nb1)) (halt-f δ₂ (π₂ (π₂ nbs)))

funda2-rec  
  {ins = ins} {A = A} {env = env} {stack = stack} {inZ = inZ} {inS = inS} {fr = fr}
  ty-ins tyZ tyS ty-env ty-st h-env h-st asm (suc n) (halt-f (Op-recS n ∷ σ) (_ , nb) ⦃ refl ⦄ ⦃ refl ⦄) 
  with Apply-split σ
... | _ , res , δ₁ , δ₂ , refl , nb' = asm (ind2 (halt-f δ₁ nb')) (halt-f δ₂ (π₂ (π₂ nbs)))
    where
      h-cloS : ∀{n} → Halt (A ⇒ A) (< env ∷ lit-n n , inS >)
      h-cloS = 
        Halt-clo tyS (Env-cons Ty-nat ty-env) 
          (λ ha → funda tyS (Env-cons (Halt-ty ha) (Env-cons Ty-nat ty-env)) Env-nil ((h-env , tt) , ha) tt ) 
          (λ ha hf → funda2 tyS (Env-cons (Halt-ty ha) (Env-cons Ty-nat ty-env)) Env-nil ((h-env , tt) , ha) tt hf )
  
      asm2' : ∀{n v fr} → Halt A v → (hf : Halt-F ⟨ app ⨾ ret , env , · ∷ < env ∷ lit-n n , inS > ∷ v , fr ⟩) → Halt A (Halt-F.res hf)
      asm2' hv (halt-f (Op-app ∷ σ) (_ , nb) ⦃ refl ⦄ ⦃ refl ⦄) with Apply-split σ
      ... | _ , res , σ₁ , σ₂ , refl , nb' =
        let nb2 = π₂ (π₂ (Not-below-⋈-inv {σ₁ = σ₁} nb refl)) in
        let eq = π₂ (∷-inj (Not-below-ret σ₂ refl nb2)) in 
        subst (Halt A) eq (π₂ (π₂ h-cloS hv) (halt-f σ₁ nb'))

      ind2 = funda2-rec (Ty-⨾ Ty-app Ty-ret) tyZ tyS ty-env (Env-cons (Ty-clo (Env-cons Ty-nat ty-env) tyS) Env-nil) h-env (tt , h-cloS) asm2' n
      
      nbs = Not-below-⋈-inv {σ₁ = δ₁} nb refl

-- Termination, by the fundamental lemma.
-- Every well-typed value is in halt.
mutual
  Halting : ⊢ v ∈ A → Halt A v
  Halting Ty-unit = tt
  Halting {A = A ⇒ B} (Ty-clo {env = env} {ins = ins} ty-env ty-ins) = 
    let h-env = Halting-E ty-env in
      Halt-clo ty-ins ty-env 
        (λ ha → funda ty-ins (Env-cons (Halt-ty ha) ty-env) Env-nil (h-env , ha) tt) 
        (λ ha hf → funda2 ty-ins (Env-cons ((Halt-ty ha)) ty-env) Env-nil (h-env , ha) tt hf)
  Halting Ty-nat = tt
  Halting (Ty-pair ta tb) = Halting ta , Halting tb

  Halting-E : env ⊨ Γ → Halt-E Γ env
  Halting-E Env-nil = tt
  Halting-E (Env-cons ta ty-env) = Halting-E ty-env , Halting ta

-- Well-formed configurations halt at the current frame.
Termination-F : WF-Config A₀ c → Halt-F c
Termination-F (well-formed ty-ins ty-env ty-st ty-fr) = 
  funda ty-ins ty-env ty-st (Halting-E ty-env) (Halting-E ty-st)

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
