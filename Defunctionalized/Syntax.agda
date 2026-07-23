module Defunctionalized.Syntax where

open import Data.Nat
open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Relation.Binary.PropositionalEquality 

open import Basic
open import Context
open import Defunctionalized.Label

infixl 20 _∷_
infixr 20 _⨾_
infixl 20 _∷<_,_,_>
infix 15 ⟨_,_,_,_⟩
infix 10 _⟶_
infix 10 _⟶*_
infix 30 _,,_

{- Pre-syntax -}
mutual
  data Instr : Set where
    -- Core language
    pop swap app unit : Instr
    var st : ∀{Γ A} → Var Γ A → Instr
    clo : ∀{D Δ A} → ℕ → LVar D Δ A → Instr
    -- Natural numbers
    lit : ℕ → Instr
    suc add mult : Instr
    rec : ∀{D Δ A} → LVar D Δ A → LVar D (Δ ∷ Nat ∷ A) A → Instr 
    -- Pairs
    pair fst snd : Instr

  data Is : Set where
    ret : Is
    _⨾_ : Instr → Is → Is

{- Machine configuration -} 

data Block : Set where
  · : Block
  _∷_ : Block → Is → Block

{- Machine configuration -}

mutual
  data Val : Set where
    <> : Val
    lit-n : ℕ → Val
    <_,_> : ∀{D Δ A} → Env → LVar D Δ A → Val
    _,,_ : Val → Val → Val

  data Env : Set where
    · : Env
    _∷_ : Env → Val → Env

data Frame : Set where
  · : Frame
  _∷<_,_,_> : Frame → Env → Env → Is → Frame

record Config (bl : Block) : Set where
  constructor ⟨_,_,_,_⟩
  field
    ins : Is
    env stack : Env
    fr : Frame


private variable
  bl bl' : Block
  ins ins' ins'' : Is
  v v' v'' : Val
  env env' env'' stack stack' stack'' : Env
  fr fr' : Frame
  m m' n n' : ℕ

{- Operational semantics -}

data [_↦_]∈_ : ∀{Γ A} → Var Γ A → Val → Env → Set where
  hd : ∀{Γ A} → [ v₀ {Γ} {A} ↦ v ]∈ (env ∷ v)
  tl : ∀{Γ A B}{x : Var Γ A} → [ x ↦ v ]∈ env → [ vs {B = B} x ↦ v ]∈ (env ∷ v')

data ⟦_↦_⟧∈_ : ∀{D Δ A} → LVar D Δ A → Is → Block → Set where
  hd : ∀{D Δ A} → ⟦ ℓ₀ {D} {Δ} {A} ↦ ins ⟧∈ (bl ∷ ins)
  tl : ∀{D Δ A Δ' A'}{ℓ : LVar D Δ A} → 
    ⟦ ℓ ↦ ins ⟧∈ bl → ⟦ ℓs {Δ' = Δ'} {A'} ℓ ↦ ins ⟧∈ (bl ∷ ins)

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

data _⟶_ {bl : Block} : Config bl → Config bl → Set where
  Op-pop : 
    ⟨ pop ⨾ ins , env , stack ∷ v , fr ⟩ ⟶ 
    ⟨ ins       , env , stack     , fr ⟩ 
  Op-swap : 
    ⟨ swap ⨾ ins , env , stack ∷ v ∷ v' , fr ⟩ ⟶ 
    ⟨ ins        , env , stack ∷ v' ∷ v , fr ⟩ 
  Op-unit :
    ⟨ unit ⨾ ins , env , stack      , fr ⟩ ⟶ 
    ⟨ ins        , env , stack ∷ <> , fr ⟩  
  Op-clo : ∀{D Δ A B n s1 s2} → 
    {ℓ : LVar D (Δ ∷ A) B} → 
    stack ≡ (s1 ⋈e s2) → 
    len-E s2 ≡ n → 
    ⟨ clo n ℓ ⨾ ins' , env , stack            , fr ⟩ ⟶
    ⟨ ins'            , env , s1 ∷ < s2 , ℓ > , fr ⟩  
  Op-app : ∀{D Δ A B} → 
    {ℓ : LVar D (Δ ∷ A) B} →
    ⟦ ℓ ↦ ins' ⟧∈ bl → 
    ⟨ app ⨾ ins , env       , stack ∷ < env' , ℓ > ∷ v , fr ⟩ ⟶ 
    ⟨ ins'      , env' ∷ v , ·                            , fr ∷< env , stack , ins > ⟩ 
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
  Op-recZ : ∀{D Δ A} → 
    {ℓz : LVar D Δ A} → 
    {ℓs : LVar D (Δ ∷ Nat ∷ A) A} → 
    ⟦ ℓz ↦ ins' ⟧∈ bl → 
    ⟨ rec ℓz ℓs ⨾ ins , env , stack ∷ lit-n zero    , fr ⟩ ⟶
    ⟨ ins'            , env , ·                     , fr ∷< env , stack , ins > ⟩
  Op-recS : ∀{D Δ A} → 
    {ℓz : LVar D Δ A} → 
    {ℓs : LVar D (Δ ∷ Nat ∷ A) A} → 
    ⟦ ℓs ↦ ins' ⟧∈ bl → 
    ⟨ rec ℓz ℓs ⨾ ins , env , stack ∷ lit-n (suc n)    , fr ⟩ ⟶
    ⟨ rec ℓz ℓs ⨾ app ⨾ ret   , env , · ∷ < (env ∷ lit-n n) , ℓs > ∷ lit-n n , fr ∷< env , stack , ins > ⟩
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

data _⟶*_ {bl : Block} : Config bl → Config bl → Set where
  ε : ∀{c} → c ⟶* c
  _∷_ : ∀{c c' c''} → c ⟶ c' → c' ⟶* c'' → c ⟶* c''

private variable
  c c' c'' c₀ c₁ : Config bl

_⋈_ : (c ⟶* c') → (c' ⟶* c'') → (c ⟶* c'')
ε ⋈ σ' = σ'
(a ∷ σ) ⋈ σ' = a ∷ (σ ⋈ σ')

{- The apply-split lemma -}

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

-- Not-below-pred : {σ : c ⟶* c'} → Not-below (fr ∷< env , stack , ins >) σ → Not-below fr σ
-- Not-below-pred {σ = ε} fr< = ≤ᵣ-pred fr<
-- Not-below-pred {σ = a ∷ σ} (fr< , nb) = (≤ᵣ-pred fr<) , (Not-below-pred nb)

-- Not-below-⋈ : {fr-base : Frame}{σ : c ⟶* c'}{σ' : c' ⟶* c''} → 
--   Not-below fr-base σ → Not-below fr-base σ' → Not-below fr-base (σ ⋈ σ')
-- Not-below-⋈ {σ = ε} {σ'} nb nb' = nb'
-- Not-below-⋈ {σ = a ∷ σ} {σ'} (fr< , nb) nb' = fr< , Not-below-⋈ nb nb'

-- Not-below-⋈-inv : 
--   {fr-base : Frame}{σ : c ⟶* c'}{σ₁ : c ⟶* c''}{σ₂ : c'' ⟶* c'} → 
--   Not-below fr-base σ → σ ≡ σ₁ ⋈ σ₂ → Not-below fr-base σ₁ × Not-below fr-base σ₂
-- Not-below-⋈-inv {σ₁ = ε} {σ₂ = ε} fr< refl = fr< , fr<  
-- Not-below-⋈-inv {σ₁ = ε} {σ₂ = a ∷ σ₂} (fr< , nb) refl = fr< , fr< , nb
-- Not-below-⋈-inv {σ₁ = a ∷ σ₁} {σ₂ = σ₂} (fr< , nb) refl = (fr< , π₁ (Not-below-⋈-inv nb refl)) , π₂ (Not-below-⋈-inv nb refl)

-- Not-below-ret : (σ : ⟨ ret , env , stack , fr ⟩ ⟶* ⟨ ret , env' , stack' , fr' ⟩) → fr ≡ fr' → Not-below fr σ → stack ≡ stack'
-- Not-below-ret ε eq nb = refl
-- Not-below-ret (Op-ret ∷ (_ ∷ σ)) refl (_ , fr< , nb) = absurd (≤ᵣ-cons-neq fr<)

