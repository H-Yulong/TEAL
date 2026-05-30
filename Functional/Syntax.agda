module Functional.Syntax where

open import Data.Nat
open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Relation.Binary.PropositionalEquality 

open import Basic
open import Context

infixl 20 _∷_
infixr 20 _⨾_
infixl 20 _∷<_,_,_>
infix 5 _<ᵣ_
infix 5 _<ₛ_
infixl 30 _,,_

{- Pre-syntax -}

mutual
  data Instr : Set where
    -- Core language
    pop swap app unit : Instr
    var st : ∀{Γ A} → Var Γ A → Instr
    pushc : Is → Instr
    clo : ℕ → Is → Instr
    -- Natural numbers
    lit : ℕ → Instr
    suc add mult : Instr
    rec : Is → Is → Instr 
    -- Pairs
    pair fst snd : Instr

  data Is : Set where
    ret : Is
    _⨾_ : Instr → Is → Is

{- Machine configuration -}

mutual
  data Val : Set where
    <> : Val
    lit-n : ℕ → Val
    <_,_> : Env → Is → Val
    _,,_ : Val → Val → Val

  data Env : Set where
    · : Env
    _∷_ : Env → Val → Env

data Frame : Set where
  · : Frame
  _∷<_,_,_> : Frame → Env → Env → Is → Frame

record Config : Set where
  constructor ⟨_,_,_,_⟩
  field
    ins : Is
    env stack : Env
    fr : Frame

private variable
  ins ins' ins'' : Is
  v v' v'' : Val
  env env' env'' stack stack' stack'' : Env
  fr fr' : Frame
  m m' n n' : ℕ

{- Operational semantics -}

data [_↦_]∈_ : ∀{Γ A} → Var Γ A → Val → Env → Set where
  hd : ∀{Γ A} → [ v₀ {Γ} {A} ↦ v ]∈ (env ∷ v)
  tl : ∀{Γ A B}{x : Var Γ A} → [ x ↦ v ]∈ env → [ vs {B = B} x ↦ v ]∈ (env ∷ v')

[↦]∈-inj : ∀{Γ A}{x : Var Γ A} → [ x ↦ v ]∈ env → [ x ↦ v' ]∈ env → v ≡ v'
[↦]∈-inj hd hd = refl
[↦]∈-inj (tl c) (tl c') = [↦]∈-inj c c'

len-E : Env → ℕ
len-E · = zero
len-E (env ∷ _) = suc (len-E env)

_⋈e_ : Env → Env → Env
env ⋈e · = env
env ⋈e (env' ∷ v) = (env ⋈e env') ∷ v

∷-inj : env ∷ v ≡ env' ∷ v' → (env ≡ env') × (v ≡ v')
∷-inj refl = refl , refl

split-len : ∀{s s' t t'} → s ⋈e s' ≡ t ⋈e t' → len-E s' ≡ len-E t' → (s ≡ t) × (s' ≡ t')
split-len {s' = ·} {t' = ·} pf len= = pf , refl
split-len {s' = s' ∷ x} {t' = t' ∷ x'} pf len= = 
  let pfs = ∷-inj pf in
  let ind = split-len (π₁ pfs) (suc-inj len=) in 
    π₁ ind , cong₂ _∷_ (π₂ ind) (π₂ pfs)

data _⟶_ : Config → Config → Set where
  Op-pop : 
    ⟨ pop ⨾ ins , env , stack ∷ v , fr ⟩ ⟶ 
    ⟨ ins       , env , stack     , fr ⟩ 
  Op-swap : 
    ⟨ swap ⨾ ins , env , stack ∷ v ∷ v' , fr ⟩ ⟶ 
    ⟨ ins        , env , stack ∷ v' ∷ v , fr ⟩ 
  Op-app : 
    ⟨ app ⨾ ins , env       , stack ∷ < env' , ins' > ∷ v , fr ⟩ ⟶ 
    ⟨ ins'      , env' ∷ v , ·                            , fr ∷< env , stack , ins > ⟩ 
  Op-unit :
    ⟨ unit ⨾ ins , env , stack      , fr ⟩ ⟶ 
    ⟨ ins        , env , stack ∷ <> , fr ⟩  
  Op-pushc : 
    ⟨ pushc ins ⨾ ins' , env , stack                  , fr ⟩ ⟶ 
    ⟨ ins'             , env , stack ∷ < env , ins > , fr ⟩ 
  Op-clo : ∀{n s1 s2} → 
    stack ≡ (s1 ⋈e s2) → 
    len-E s2 ≡ n → 
    ⟨ clo n ins ⨾ ins' , env , stack            , fr ⟩ ⟶
    ⟨ ins'            , env , s1 ∷ < s2 , ins > , fr ⟩
  Op-ret :
    ⟨ ret  , env  , stack ∷ v  , fr ∷< env' , stack' , ins' > ⟩ ⟶ 
    ⟨ ins' , env' , stack' ∷ v , fr ⟩
  Op-var : ∀{Γ A} → 
    {x : Var Γ A} → [ x ↦ v ]∈ env → 
    ⟨ var x ⨾ ins , env , stack     , fr ⟩ ⟶ 
    ⟨ ins         , env , stack ∷ v , fr ⟩ 
  Op-st : ∀{Γ A} → 
    {x : Var Γ A} → [ x ↦ v ]∈ stack → 
    ⟨ st x ⨾ ins , env , stack     , fr ⟩ ⟶ 
    ⟨ ins        , env , stack ∷ v , fr ⟩ 
  Op-lit : 
    (n : ℕ) →
    ⟨ lit n ⨾ ins , env , stack          , fr ⟩ ⟶ 
    ⟨ ins         , env , stack ∷ lit-n n , fr ⟩ 
  Op-suc : 
    ⟨ suc ⨾ ins , env , stack ∷ lit-n n       , fr ⟩ ⟶ 
    ⟨ ins       , env , stack ∷ lit-n (suc n) , fr ⟩ 
  Op-recZ : 
    ⟨ rec ins ins' ⨾ ins'' , env , stack ∷ lit-n zero    , fr ⟩ ⟶
    ⟨ ins                  , env , ·                     , fr ∷< env , stack , ins'' > ⟩
  Op-recS : 
    (n : ℕ) → 
    ⟨ rec ins ins' ⨾ ins''       , env , stack ∷ lit-n (suc n)            , fr ⟩ ⟶
    ⟨ rec ins ins' ⨾ app ⨾ ret   , env , · ∷ < (env ∷ lit-n n) , ins' > ∷ lit-n n , fr ∷< env , stack , ins'' > ⟩
  Op-add : 
    (m n : ℕ) → 
    ⟨ add ⨾ ins , env , stack ∷ lit-n m ∷ lit-n n , fr ⟩ ⟶ 
    ⟨ ins       , env , stack ∷ lit-n (m + n)     , fr ⟩ 
  Op-mult : 
    (m n : ℕ) → 
    ⟨ mult ⨾ ins , env , stack ∷ lit-n m ∷ lit-n n , fr ⟩ ⟶ 
    ⟨ ins       , env , stack ∷ lit-n (m * n)     , fr ⟩ 
  Op-pair : 
    ⟨ pair ⨾ ins , env , stack ∷ v ∷ v'  , fr ⟩ ⟶
    ⟨ ins        , env , stack ∷ v ,, v' , fr ⟩
  Op-fst : 
    ⟨ fst ⨾ ins , env , stack ∷ v ,, v' , fr ⟩ ⟶
    ⟨ ins       , env , stack ∷ v       , fr ⟩
  Op-snd : 
    ⟨ snd ⨾ ins , env , stack ∷ v ,, v' , fr ⟩ ⟶
    ⟨ ins       , env , stack ∷ v'      , fr ⟩

data _⟶*_ : Config → Config → Set where
  ε : ∀{c} → c ⟶* c
  _∷_ : ∀{c c' c''} → c ⟶ c' → c' ⟶* c'' → c ⟶* c''

private variable
  c c' c'' c₀ c₁ : Config

_⋈_ : (c ⟶* c') → (c' ⟶* c'') → (c ⟶* c'')
ε ⋈ σ' = σ'
(a ∷ σ) ⋈ σ' = a ∷ (σ ⋈ σ')

{- The apply-split lemma -}

{-
The apply-split lemma states that: if the machine pops one stack frame, then it must have been a return instruction somewhere.
Formally:
  Given a trace σ : ⟨ ins , env , stack , fr ∷< env' , stack' , ins' > ⟩ ⟶* ⟨ ret , env' , stack'' ∷ v , fr ⟩ 
    where one call frame is popped, 
    we can break the sequence σ into σ₁ ∷ Op-ret ∷ σ₂ such that
    - dump , res is the final stack shape of σ₁ (before the return instruction)
    - no step in σ₁ reduces the frame lower than fr ∷< env' , stack' , ins' >
      (i.e. the return is the first instruction that pops the frame < env' , stack' , ins' >).

This lemma is particually helpful in termination proofs, where we need to break down a trace like this in the apply case,
to show that (by I.H.) the top closure's return value is in Halt.

This lemma cannot be proven directly, the I.H is not strong enough at the apply case. 

lemma :
  (σ : ⟨ ins , env , stack , fr ∷< env' , stack' , ins' > ⟩ ⟶* ⟨ ret , env' , stack'' ∷ v , fr ⟩) →
  Σ Env (λ dump → 
  Σ Val (λ res →
    ⟨ ins , env , stack , fr ∷< env' , stack' , ins' > ⟩ ⟶* ⟨ ret , env , dump ∷ res , fr ∷< env' , stack' , ins' > ⟩ × 
    ⟨ ins' , env' , stack' ∷ res  , fr ⟩ ⟶* ⟨ ret , env' , stack'' ∷ v , fr ⟩))
lemma (Op-app ∷ σ) = {! σ !}

We need to generalize over fr, let it become some fr' smaller than the starting frames.

lemma : 
  (σ : ⟨ ins , env , stack , fr ∷< env'' , stack'' , ins'' > ⟩ ⟶* ⟨ ins' , env' , stack' , fr' ⟩) →
  fr' <ᵣ (fr ∷< env'' , stack'' , ins'' >) →
  Σ Env (λ dump → 
  Σ Val (λ res →
  Σ (⟨ ins , env , stack , fr ∷< env'' , stack'' , ins'' > ⟩ ⟶* ⟨ ret , env , dump ∷ res , fr ∷< env'' , stack'' , ins'' > ⟩)(λ σ₁ →
  Σ (⟨ ins'' , env'' , stack'' ∷ res  , fr ⟩ ⟶* ⟨ ins' , env' , stack' , fr' ⟩))))
lemma (Op-app ∷ σ) pf-fr with lemma σ (more pf-fr)
... | _ , _ , δ₁ , δ₂  with lemma δ₂ pf-fr 
... | dump , res , σ₁ , σ₂ = dump , res , Op-app ∷ (δ₁ ⋈ (Op-ret ∷ σ₁)) , σ₂

Now we can use I.H. on the application case. Given
  (Op-app ∷ σ) : ⟨ ins , env , stack ∷ < e , i > ∷ v , fr ∷< env'' , stack'' , ins'' > ⟩ ⟶* ⟨ ins' , env' , stack' , fr' ⟩,
it is broken down into
  ⟨ ins , env , stack ∷ < e , i > ∷ v , fr ∷< env'' , stack'' , ins'' > ⟩
  -- Op-app -->
  ⟨ i , e ∷ v , · , fr ∷< env'' , stack'' , ins'' > ∷< env , stack , ins > ⟩
  -- δ₁ -->
  ⟨ ret , e ∷ v , _ ∷ v' , fr ∷< env'' , stack'' , ins'' > ∷< env , stack , ins > ⟩
  -- Op-ret -->
  ⟨ ins , env , stack ∷ v' , fr ∷< env'' , stack'' , ins'' ⟩
  -- δ₂ -->
  ⟨ ins' , env' , stack' , fr' ⟩.
We need to further apply the lemma on δ₂, breaking it down to σ₁ ∷ Op-ret ∷ σ₂,
and return (δ₁ ∷ Op-ret ∷ σ₁) , σ₂ as the result.

The final technique we need is the well-founded induction to apply I.H. on δ­₂,
which is structurally smaller than σ.

-}

{- _<_ relation -}

data _<ₛ_ : (σ : c ⟶* c₀) → (σ' : c' ⟶* c₀) → Set where
  one  : {a : c ⟶ c'}{σ : c' ⟶* c₀} → σ <ₛ (a ∷ σ)
  more : {σ : c'' ⟶* c₀}{a : c ⟶ c'}{σ' : c' ⟶* c₀} → σ <ₛ σ' → σ <ₛ (a ∷ σ')

data _≤ᵣ_ : Frame → Frame → Set where
  zero : ⦃ eq : fr' ≡ fr ⦄ → fr ≤ᵣ fr'
  more : fr ≤ᵣ fr' → fr ≤ᵣ (fr' ∷< env , stack , ins >)

data _<ᵣ_ : Frame → Frame → Set where
  one : fr <ᵣ (fr ∷< env , stack , ins >)
  more : fr <ᵣ fr' → fr <ᵣ (fr' ∷< env , stack , ins >)

<ₛ-trans : {σ : c ⟶* c₀}{σ' : c' ⟶* c₀}{σ'' : c'' ⟶* c₀} →  
  σ <ₛ σ' → σ' <ₛ σ'' → σ <ₛ σ''
<ₛ-trans pf one = more pf
<ₛ-trans pf (more pf') = more (<ₛ-trans pf pf')

<ᵣ-pred : (fr ∷< env , stack , ins >) <ᵣ fr' → fr <ᵣ fr'
<ᵣ-pred one = more one
<ᵣ-pred (more pf) = more (<ᵣ-pred pf)

<ᵣ-cons-neq : (fr ∷< env , stack , ins >) <ᵣ fr → ⊥
<ᵣ-cons-neq (more pf) = <ᵣ-cons-neq (<ᵣ-pred pf)

≤ᵣ-pred : (fr ∷< env , stack , ins >) ≤ᵣ fr' → fr ≤ᵣ fr'
≤ᵣ-pred (zero ⦃ refl ⦄) = more zero
≤ᵣ-pred (more pf) = more (≤ᵣ-pred pf)

≤ᵣ-cons-neq : (fr ∷< env , stack , ins >) ≤ᵣ fr → ⊥
≤ᵣ-cons-neq (more pf) = ≤ᵣ-cons-neq (≤ᵣ-pred pf)

dropᵣ : (fr fr' : Frame) → fr ≤ᵣ fr' → Frame
dropᵣ fr fr' zero = ·
dropᵣ fr (fr' ∷< env , stack , ins >) (more pf) = (dropᵣ fr fr' pf) ∷< env , stack , ins >

{- Accessibility relation -}

data Acc (σ : c ⟶* c') : Set where
  acc : (∀{c''}{σ' : c'' ⟶* c'} → σ' <ₛ σ → Acc σ') → Acc σ

<ₛ-Acc : (σ : c ⟶* c') → Acc σ
<ₛ-Acc σ = acc aux 
  where
    aux : {σ : c ⟶* c'}{σ' : c'' ⟶* c'} → σ' <ₛ σ → Acc σ'
    aux one = <ₛ-Acc _
    aux (more pf) = aux pf

{- A sequence never goes below a part of the call frame -}

Not-below : (fr-base : Frame) → ⟨ ins , env , stack , fr ⟩ ⟶* ⟨ ins' , env' , stack' , fr' ⟩ → Set
Not-below {fr = fr} fr-base ε = fr-base ≤ᵣ fr
Not-below {fr = fr} fr-base (a ∷ σ) = fr-base ≤ᵣ fr × Not-below fr-base σ

Not-below-pred : {σ : c ⟶* c'} → Not-below (fr ∷< env , stack , ins >) σ → Not-below fr σ
Not-below-pred {σ = ε} fr< = ≤ᵣ-pred fr<
Not-below-pred {σ = a ∷ σ} (fr< , nb) = (≤ᵣ-pred fr<) , (Not-below-pred nb)

Not-below-⋈ : {fr-base : Frame}{σ : c ⟶* c'}{σ' : c' ⟶* c''} → 
  Not-below fr-base σ → Not-below fr-base σ' → Not-below fr-base (σ ⋈ σ')
Not-below-⋈ {σ = ε} {σ'} nb nb' = nb'
Not-below-⋈ {σ = a ∷ σ} {σ'} (fr< , nb) nb' = fr< , Not-below-⋈ nb nb'

Not-below-⋈-inv : 
  {fr-base : Frame}{σ : c ⟶* c'}{σ₁ : c ⟶* c''}{σ₂ : c'' ⟶* c'} → 
  Not-below fr-base σ → σ ≡ σ₁ ⋈ σ₂ → Not-below fr-base σ₁ × Not-below fr-base σ₂
Not-below-⋈-inv {σ₁ = ε} {σ₂ = ε} fr< refl = fr< , fr<  
Not-below-⋈-inv {σ₁ = ε} {σ₂ = a ∷ σ₂} (fr< , nb) refl = fr< , fr< , nb
Not-below-⋈-inv {σ₁ = a ∷ σ₁} {σ₂ = σ₂} (fr< , nb) refl = (fr< , π₁ (Not-below-⋈-inv nb refl)) , π₂ (Not-below-⋈-inv nb refl)

Not-below-ret : (σ : ⟨ ret , env , stack , fr ⟩ ⟶* ⟨ ret , env' , stack' , fr' ⟩) → fr ≡ fr' → Not-below fr σ → stack ≡ stack'
Not-below-ret ε eq nb = refl
Not-below-ret (Op-ret ∷ (_ ∷ σ)) refl (_ , fr< , nb) = absurd (≤ᵣ-cons-neq fr<)

⋈-lem : 
  (σ : c ⟶* c')(a : c' ⟶ c'')(σ' : c'' ⟶* c₀)(σ'' : c₀ ⟶* c₁) → 
  σ ⋈ (a ∷ (σ' ⋈ σ'')) ≡ (σ ⋈ (a ∷ σ')) ⋈ σ''
⋈-lem ε a σ' σ'' = refl
⋈-lem (a' ∷ σ) a σ' σ'' rewrite ⋈-lem σ a σ' σ'' = refl

{- Proof of the generlaized lemma -}

App-split-lemma : 
  (σ : ⟨ ins , env , stack , fr ∷< env'' , stack'' , ins'' > ⟩ ⟶* ⟨ ins' , env' , stack' , fr' ⟩) →
  fr' <ᵣ (fr ∷< env'' , stack'' , ins'' >) →
  Acc σ →
  Σ Env (λ dump → 
  Σ Val (λ res →
  Σ (⟨ ins , env , stack , fr ∷< env'' , stack'' , ins'' > ⟩ ⟶* ⟨ ret , env , dump ∷ res , fr ∷< env'' , stack'' , ins'' > ⟩)(λ σ₁ →
  Σ (⟨ ins'' , env'' , stack'' ∷ res  , fr ⟩ ⟶* ⟨ ins' , env' , stack' , fr' ⟩) (λ σ₂ →
    σ₂ <ₛ σ × 
    σ ≡ σ₁ ⋈ (Op-ret ∷ σ₂) ×
    Not-below (fr ∷< env'' , stack'' , ins'' >) σ₁
  ))))
App-split-lemma ε (more pf-fr) (acc f) = absurd (<ᵣ-cons-neq pf-fr)
App-split-lemma (Op-pop ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-pop ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-swap ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-swap ∷ σ₁ , σ₂ , more pf< , refl  , zero , nb
App-split-lemma (Op-app ∷ σ) pf-fr (acc f) with App-split-lemma σ (more pf-fr) (f one)
... | _ , _ , δ₁ , δ₂ , pf< , refl , nb with App-split-lemma δ₂ (pf-fr) (f (more pf<)) 
... | dump , res , σ₁ , σ₂ , pf<' , refl , nb' = 
  dump , res , Op-app ∷ (δ₁ ⋈ (Op-ret ∷ σ₁)) , σ₂ , <ₛ-trans pf<' (more pf<) , 
  cong (λ x → Op-app ∷ x) (⋈-lem δ₁ Op-ret σ₁ (Op-ret ∷ σ₂)) ,
  zero , Not-below-⋈ {σ = δ₁} (Not-below-pred nb) (more zero , nb')
App-split-lemma (Op-unit ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-unit ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-pushc ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-pushc ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-clo pf len< ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , (Op-clo pf len<) ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-ret ∷ σ) pf-fr (acc f) = _ , _ , ε , σ , one , refl , zero
App-split-lemma (Op-var access ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-var access ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-st access ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-st access ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-lit n ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-lit n ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-suc ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-suc ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-recZ ∷ σ) pf-fr (acc f) with App-split-lemma σ (more pf-fr) (f one)
... | _ , res , δ₁ , δ₂ , pf< , refl , nb with App-split-lemma δ₂ (pf-fr) (f (more pf<)) 
... | dump , res' , σ₁ , σ₂ , pf<' , refl , nb' = 
  dump , res' , Op-recZ ∷ (δ₁ ⋈ (Op-ret ∷ σ₁)) , σ₂ , <ₛ-trans pf<' (more pf<) , 
  cong (λ x → Op-recZ ∷ x) (⋈-lem δ₁ Op-ret σ₁ (Op-ret ∷ σ₂)) , 
  zero , Not-below-⋈ {σ = δ₁} (Not-below-pred nb) (more zero , nb')
App-split-lemma (Op-recS n ∷ σ) pf-fr (acc f) with App-split-lemma σ (more pf-fr) (f one)
... | _ , res , δ₁ , δ₂ , pf< , refl , nb with App-split-lemma δ₂ (pf-fr) (f (more pf<)) 
... | dump , res' , σ₁ , σ₂ , pf<' , refl , nb' = 
  dump , res' , (Op-recS n) ∷ (δ₁ ⋈ (Op-ret ∷ σ₁)) , σ₂ , <ₛ-trans pf<' (more pf<) , 
  cong (λ x → (Op-recS n) ∷ x) (⋈-lem δ₁ Op-ret σ₁ (Op-ret ∷ σ₂)) , 
  zero , Not-below-⋈ {σ = δ₁} (Not-below-pred nb) (more zero , nb')
App-split-lemma (Op-add m n ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-add m n ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-mult m n ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-mult m n ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-pair ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-pair ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-fst ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-fst ∷ σ₁ , σ₂ , more pf< , refl , zero , nb
App-split-lemma (Op-snd ∷ σ) pf-fr (acc f) with App-split-lemma σ pf-fr (f one)
... | dump , res , σ₁ , σ₂ , pf< , refl , nb = dump , res , Op-snd ∷ σ₁ , σ₂ , more pf< , refl , zero , nb

Apply-split : 
  (σ : ⟨ ins , env , stack , fr ∷< env' , stack' , ins' > ⟩ ⟶* ⟨ ret , env' , stack'' ∷ v , fr ⟩) →
  Σ Env (λ dump → 
  Σ Val (λ res →
  Σ (⟨ ins , env , stack , fr ∷< env' , stack' , ins' > ⟩ ⟶* ⟨ ret , env , dump ∷ res , fr ∷< env' , stack' , ins' > ⟩)(λ σ₁ →
  Σ (⟨ ins' , env' , stack' ∷ res  , fr ⟩ ⟶* ⟨ ret , env' , stack'' ∷ v , fr ⟩) (λ σ₂ →
    σ ≡ σ₁ ⋈ (Op-ret ∷ σ₂) ×
    Not-below (fr ∷< env' , stack' , ins' >) σ₁
  ))))
Apply-split σ with App-split-lemma σ one (<ₛ-Acc σ)
... | dump , res , σ₁ , σ₂ , _ , eq , nb = dump , res , σ₁ , σ₂ , eq , nb

{- Halting -}

data _↓_ : Config → Val → Set where
  halt-frame : 
    ⟨ ins , env , stack , fr ⟩ ⟶* ⟨ ret , env , stack' ∷ v , fr ⟩ →
    ⟨ ins , env , stack , fr ⟩ ↓ v

data _⇓_ : Config → Val → Set where
  halt : c ⟶* ⟨ ret , env , stack ∷ v , · ⟩ → c ⇓ v

data _⇓₀_,_ : Config → Val → ℕ → Set where
  finish : ⟨ ret , env , stack ∷ v , · ⟩ ⇓₀ v , zero
  step : ∀{n} → c' ⇓₀ v , n → c ⟶ c' → c ⇓₀ v , (suc n)

⇓-cons : c ⟶ c' → c' ⇓ v → c ⇓ v
⇓-cons a (halt σ) = halt (a ∷ σ)

⇓-count : c ⟶* ⟨ ret , env , stack ∷ v , · ⟩ → Σ ℕ (λ n → c ⇓₀ v , n)
⇓-count ε = zero , finish
⇓-count (op ∷ σ) = 
  let ind = ⇓-count σ in
    suc (π₁ ind) , step (π₂ ind) op

{- Determinacy -}

Determinacy : c ⟶ c' → c ⟶ c'' → c' ≡ c''
Determinacy Op-pop Op-pop = refl
Determinacy Op-swap Op-swap = refl
Determinacy Op-app Op-app = refl
Determinacy Op-unit Op-unit = refl
Determinacy Op-pushc Op-pushc = refl
Determinacy {c = c} (Op-clo pf len<) (Op-clo pf' len<') 
  with (split-len (trans (sym pf) pf') (trans len< (sym len<')))
... | refl , refl = refl
Determinacy Op-ret Op-ret = refl
Determinacy (Op-var x) (Op-var x') rewrite [↦]∈-inj x x' = refl
Determinacy (Op-st x) (Op-st x') rewrite [↦]∈-inj x x' = refl
Determinacy (Op-lit n) (Op-lit n) = refl
Determinacy Op-suc Op-suc = refl
Determinacy Op-recZ Op-recZ = refl
Determinacy (Op-recS n) (Op-recS n) = refl
Determinacy (Op-add m n) (Op-add m n) = refl
Determinacy (Op-mult m n) (Op-mult m n) = refl
Determinacy Op-pair Op-pair = refl
Determinacy Op-fst Op-fst = refl
Determinacy Op-snd Op-snd = refl

Determinacy-V : c ⇓ v → c ⇓ v' → v ≡ v'
Determinacy-V (halt σ) (halt σ') = lem σ σ'
  where
    lem : 
      c ⟶* ⟨ ret , env , stack ∷ v , · ⟩ → 
      c ⟶* ⟨ ret , env' , stack' ∷ v' , · ⟩ → 
      v ≡ v'
    lem ε ε = refl
    lem (op ∷ σ) (op' ∷ σ') rewrite Determinacy op op' = lem σ σ'

step-red : c ⇓₀ v , (suc n) → c ⟶ c' → c' ⇓₀ v , n
step-red (step finish op) op' rewrite Determinacy op' op = finish
step-red (step (step σ a) op) op' rewrite Determinacy op' op = step σ a
