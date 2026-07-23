module Functional.TypeMachine.Intrinsic where

open import Basic
open import Context

open import Data.Nat
open import Data.Product renaming (proj₁ to π₁; proj₂ to π₂) hiding (swap; <_,_>)
open import Data.Sum hiding (swap)
open import Relation.Binary.PropositionalEquality 

import Functional.Syntax as S
import Functional.TypeMachine.Types as T
import Functional.TypeMachine.Termination as H

open S using ([_↦_]∈_; _⇓₀_,_)
open T using (_⊢ᵢ_∈_⟶_; _⊢_∈_⟶_; ⊢_∈_; _⊨_; _⊢ᵣ_∈_⟶_ )

private variable
  @0 Γ Γ' Γ'' Δ Δ' Δ'' : Con
  @0 A A' B B' C C' A₀ : Ty

infixl 20 _∷_
infixr 20 _⨾_

data Instr : @0 Con → @0 Con → @0 Con → Set
data Is : @0 Con → @0 Con → @0 Con → Set

data Instr where
  pop : Instr Γ (Δ ∷ A) Δ
  swap : Instr Γ (Δ ∷ A ∷ B) (Δ ∷ B ∷ A)
  app : Instr Γ (Δ ∷ (A ⇒ B) ∷ A) (Δ ∷ B)
  unit : Instr Γ Δ (Δ ∷ One)
  var : (x : Var Γ A) → Instr Γ Δ (Δ ∷ A)
  st :(x : Var Δ A) → Instr Γ Δ (Δ ∷ A)
  pushc : Is (Γ ∷ A) · (Δ' ∷ B) → Instr Γ Δ (Δ ∷ A ⇒ B)
  lit : (n : ℕ) → Instr Γ Δ (Δ ∷ Nat)
  suc : Instr Γ (Δ ∷ Nat) (Δ ∷ Nat)
  rec : 
    Is Γ · (Δ ∷ A) → 
    Is (Γ ∷ Nat ∷ A) · (Δ' ∷ A) → 
    Instr Γ (Δ'' ∷ Nat) (Δ'' ∷ A)
  add : Instr Γ (Δ ∷ Nat ∷ Nat) (Δ ∷ Nat)
  mult : Instr Γ (Δ ∷ Nat ∷ Nat) (Δ ∷ Nat)
  pair : Instr Γ (Δ ∷ A ∷ B) (Δ ∷ A ⊗ B)
  fst : Instr Γ (Δ ∷ A ⊗ B) (Δ ∷ A)
  snd : Instr Γ (Δ ∷ A ⊗ B) (Δ ∷ B)

data Is where
  ret : Is Γ (Δ ∷ A) (Δ ∷ A)
  _⨾_ : Instr Γ Δ Δ' → Is Γ Δ' Δ'' → Is Γ Δ Δ''

data Env : @0 Con → Set
data Val : @0 Ty → Set

data Env where
  · : Env ·
  _∷_ : Env Γ → Val A → Env (Γ ∷ A)

data Val where
  <> : Val One
  <_,_> : Env Γ → Is (Γ ∷ A) · (Δ ∷ B) → Val (A ⇒ B)
  lit-n : (n : ℕ) → Val Nat
  _,,_ : Val A → Val B → Val (A ⊗ B)

data Fr : @0 Con → @0 Ty → @0 Ty → Set where
  · : Fr · A₀ A₀
  _∷<_,_,_> : 
    (fr : Fr Γ' B A₀) → 
    (ins : Is Γ (Δ ∷ A) (Δ' ∷ B)) → 
    (env : Env Γ) →
    (stack : Env Δ) → 
    Fr Γ A A₀

record Config (@0 A₀ : Ty) : Set where
  constructor ⟨_,_,_,_⟩
  field
    @0 {cΓ cΓ' cΔ cΔ'} : Con
    @0 {cA} : Ty
    ins : Is cΓ cΔ (cΔ' ∷ cA) 
    env : Env cΓ
    stack : Env cΔ
    fr : Fr cΓ' cA A₀

find-var : ∀{@0 Γ A} → Var Γ A → Env Γ → Val A
find-var v₀ (env ∷ v) = v
find-var (vs x) (env ∷ v) = find-var x env

-- Take one step for a machine. Does nothing if machine halts.
step : Config A₀ → Config A₀
step ⟨ ins , env , stack , fr ⟩ = step' ins env stack fr
  where    
    step' :
      (ins : Is Γ Δ (Δ' ∷ A)) →
      (env : Env Γ) → 
      (stack : Env Δ) → 
      (fr : Fr Γ' A A₀) →
      Config A₀
    step' ret env (stack ∷ v) · = ⟨ ret , env , (stack ∷ v) , · ⟩
    step' ret env (stack ∷ v) (fr ∷< ins' , env' , stack' >) = ⟨ ins' , env' , (stack' ∷ v) , fr ⟩
    step' (pop ⨾ ins) env (stack ∷ v) fr = ⟨ ins , env , stack , fr ⟩
    step' (swap ⨾ ins) env (stack ∷ v ∷ v') fr = ⟨ ins , env , (stack ∷ v' ∷ v) , fr ⟩
    step' (app ⨾ ins) env (stack ∷ < env' , ins' > ∷ v) fr = ⟨ ins' , env' ∷ v , · , fr ∷< ins , env , stack > ⟩
    step' (unit ⨾ ins) env stack fr = ⟨ ins , env , stack ∷ <> , fr ⟩
    step' (var x ⨾ ins) env stack fr = ⟨ ins , env , stack ∷ find-var x env , fr ⟩
    step' (st x ⨾ ins) env stack fr = ⟨ ins , env , stack ∷ find-var x stack , fr ⟩
    step' (pushc ins ⨾ ins') env stack fr = ⟨ ins' , env , stack ∷ < env , ins > , fr ⟩
    step' (lit n ⨾ ins) env stack fr = ⟨ ins , env , stack ∷ lit-n n , fr ⟩
    step' (suc ⨾ ins) env (stack ∷ lit-n n) fr = ⟨ ins , env , stack ∷ lit-n (suc n) , fr ⟩
    step' (rec iz is ⨾ ins) env (stack ∷ lit-n zero) fr = ⟨ iz , env , · , (fr ∷< ins , env , stack >) ⟩
    step' (rec iz is ⨾ ins) env (stack ∷ lit-n (suc n)) fr = 
      ⟨ rec iz is ⨾ app ⨾ ret , env , · ∷ < env ∷ lit-n n , is > ∷ lit-n n , (fr ∷< ins , env , stack >) ⟩
    step' (add ⨾ ins) env (stack ∷ lit-n m ∷ lit-n n) fr = ⟨ ins , env , stack ∷ lit-n (m + n) , fr ⟩
    step' (mult ⨾ ins) env (stack ∷ lit-n m ∷ lit-n n) fr = ⟨ ins , env , stack ∷ lit-n (m * n) , fr ⟩
    step' (pair ⨾ ins) env (stack ∷ v ∷ v') fr = ⟨ ins , env , stack ∷ (v ,, v') , fr ⟩
    step' (fst ⨾ ins) env (stack ∷ (v ,, v')) fr = ⟨ ins , env , stack ∷ v , fr ⟩
    step' (snd ⨾ ins) env (stack ∷ (v ,, v')) fr = ⟨ ins , env , stack ∷ v' , fr ⟩

-- Transformation back to extrinsic machine
@0 transform-i : Instr Γ Δ Δ' → Σ S.Instr (λ i → Γ ⊢ᵢ i ∈ Δ ⟶ Δ')
@0 transform : Is Γ Δ Δ' → Σ S.Is (λ ins → Γ ⊢ ins ∈ Δ ⟶ Δ')

transform-i pop = S.pop , T.Ty-pop
transform-i swap = S.swap , T.Ty-swap
transform-i app = S.app , T.Ty-app
transform-i unit = S.unit , T.Ty-unit
transform-i (var x) = S.var x , T.Ty-var x
transform-i (st x) = S.st x , T.Ty-st x
transform-i (pushc ins) = 
  let ins , ty-ins = transform ins in
    S.pushc ins , T.Ty-pushc ty-ins
transform-i (lit n) = S.lit n , T.Ty-lit n
transform-i suc = S.suc , T.Ty-suc
transform-i (rec iz is) = 
  let iz , tyZ = transform iz in
  let is , tyS = transform is in
    S.rec iz is , T.Ty-rec tyZ tyS
transform-i add = S.add , T.Ty-add
transform-i mult = S.mult , T.Ty-mult
transform-i pair = S.pair , T.Ty-pair
transform-i fst = S.fst , T.Ty-fst
transform-i snd = S.snd , T.Ty-snd

transform ret = S.ret , T.Ty-ret
transform (i ⨾ ins) = 
  let i , ty-i = transform-i i in
  let ins , ty-ins = transform ins in 
    (i S.⨾ ins) , T.Ty-⨾ ty-i ty-ins

@0 transform-E : Env Γ → Σ S.Env (λ env → env ⊨ Γ)
@0 transform-V : Val A → Σ S.Val (λ v → ⊢ v ∈ A)

transform-E · = S.· , T.Env-nil
transform-E (env ∷ v) = 
  let env , ty-env = transform-E env in 
  let v , tv = transform-V v in
    (env S.∷ v) , (T.Env-cons tv ty-env)

transform-V <> = S.<> , T.Ty-unit
transform-V < env , ins > = 
  let env , ty-env = transform-E env in 
  let ins , ty-ins = transform ins in
    S.< env , ins > , T.Ty-clo ty-env ty-ins
transform-V (lit-n n) = S.lit-n n , T.Ty-nat
transform-V (v ,, v') = 
  let v , tv = transform-V v in 
  let v' , tv' = transform-V v' in
    (v S.,, v') , T.Ty-pair tv tv'

@0 transform-F : Fr Γ A A₀ → Σ S.Frame (λ fr → Γ ⊢ᵣ fr ∈ A ⟶ A₀)
transform-F · = S.· , T.Frame-nil
transform-F (fr ∷< ins , env , stack >) = 
  let fr , ty-fr = transform-F fr in
  let ins , ty-ins = transform ins in
  let env , ty-env = transform-E env in
  let stack , ty-st = transform-E stack in
    fr S.∷< env , stack , ins > , T.Frame-cons ty-fr ty-ins ty-env ty-st 

@0 transform-C : Config A₀ → Σ S.Config (λ c → T.WF-Config A₀ c)
transform-C ⟨ ins , env , stack , fr ⟩ = 
  let ins , ty-ins = transform ins in
  let env , ty-env = transform-E env in
  let stack , ty-st = transform-E stack in
  let fr , ty-fr = transform-F fr in
    S.⟨ ins , env , stack , fr ⟩ , T.well-formed ty-ins ty-env ty-st ty-fr

data Halt? {@0 A₀ : Ty} (@0 c : Config A₀) : (@0 n : ℕ) → Set where
  stop : ∀{@0 v} → @0 (π₁ (transform-C c)) ⇓₀ v , zero → Halt? c zero
  go : ∀{@0 v n} → @0 (π₁ (transform-C c)) ⇓₀ v , (suc n) → Halt? c (suc n)

record Config-exe (@0 cA₀ : Ty) (@0 n : ℕ) : Set where
  constructor conf-exe
  field
    -- The configuration itself
    c : Config cA₀
    -- Whether the machine is at halt, carrying an erased
    -- termination proof. Essentially a bool.
    ht : Halt? c n

@0 Termination : (c : Config A₀) → Σ S.Val (λ v → Σ ℕ (λ n → π₁ (transform-C c) ⇓₀ v , n))
Termination c = H.Termination-n (π₂ (transform-C c))

@0 find-var-preserve : ∀{v} → 
  (x : Var Γ A) → (env : Env Γ) → 
  [ x ↦ v ]∈ (π₁ (transform-E env)) → π₁ (transform-V (find-var x env)) ≡ v
find-var-preserve v₀ (env ∷ v) S.hd = refl
find-var-preserve (vs x) (env ∷ v) (S.tl pf) = find-var-preserve x env pf

-- Step preserves operational semantics
@0 step-preserve : ∀{c'} → (c : Config A₀) → π₁ (transform-C c) S.⟶ c' → c' ≡ π₁ (transform-C (step c))
step-preserve ⟨ ret , env , stack ∷ x , fr ∷< ins' , env' , stack' > ⟩ S.Op-ret = refl
step-preserve ⟨ pop ⨾ ins , env , stack ∷ v , fr ⟩ S.Op-pop = refl
step-preserve ⟨ swap ⨾ ins , env , stack ∷ v ∷ v' , fr ⟩ S.Op-swap = refl
step-preserve ⟨ app ⨾ ins , env , stack ∷ < env' , ins' > ∷ v , fr ⟩ S.Op-app = refl
step-preserve ⟨ unit ⨾ ins , env , stack , fr ⟩ S.Op-unit = refl
step-preserve ⟨ var x ⨾ ins , env , stack , fr ⟩ (S.Op-var tv) 
  with find-var-preserve x env tv 
... | refl = refl
step-preserve ⟨ st x ⨾ ins , env , stack , fr ⟩ (S.Op-st tv) 
  with find-var-preserve x stack tv 
... | refl = refl
step-preserve ⟨ pushc x ⨾ ins , env , stack , fr ⟩ S.Op-pushc = refl
step-preserve ⟨ lit n ⨾ ins , env , stack , fr ⟩ (S.Op-lit n) = refl
step-preserve ⟨ suc ⨾ ins , env , stack ∷ lit-n n , fr ⟩ S.Op-suc = refl
step-preserve ⟨ rec iz is ⨾ ins , env , stack ∷ lit-n zero , fr ⟩ S.Op-recZ = refl
step-preserve ⟨ rec iz is ⨾ ins , env , stack ∷ lit-n (suc n) , fr ⟩ (S.Op-recS n) = refl
step-preserve ⟨ add ⨾ ins , env , stack ∷ lit-n m ∷ lit-n n , fr ⟩ (S.Op-add m n) = refl
step-preserve ⟨ mult ⨾ ins , env , stack ∷ lit-n m ∷ lit-n n , fr ⟩ (S.Op-mult m n) = refl
step-preserve ⟨ pair ⨾ ins , env , stack ∷ v ∷ v' , fr ⟩ S.Op-pair = refl
step-preserve ⟨ fst ⨾ ins , env , stack ∷ (v ,, v') , fr ⟩ S.Op-fst = refl
step-preserve ⟨ snd ⨾ ins , env , stack ∷ (v ,, v') , fr ⟩ S.Op-snd = refl

-- Take pred for termination proofs
@0 step-lemma : ∀{v n} → 
  (c : Config A₀) → 
  π₁ (transform-C c) ⇓₀ v , suc n → 
  π₁ (transform-C (step c)) ⇓₀ v , n
step-lemma c (S.step pf op) = subst-0 (λ z → z ⇓₀ _ , _) (step-preserve c op) pf

-- Examines the configuration, see if it is at halt
halt-lemma : ∀{@0 A₀ v n} → 
  (c : Config A₀) → 
  (@0 pf : π₁ (transform-C c) ⇓₀ v , n) → 
  Halt? c n
halt-lemma ⟨ ret , env , stack ∷ v , · ⟩ pf = 
  subst-0 (λ z → Halt? _ z) (S.step-halt pf) (stop S.finish)
halt-lemma ⟨ ret , env , stack ∷ v , fr ∷< ins' , env' , stack' > ⟩ pf = 
  subst-0 (λ z → Halt? _ z) (π₁ (π₂ (S.step-fr pf))) (go ((π₂ (π₂ (S.step-fr pf)))))
halt-lemma ⟨ i ⨾ ins , env , stack , fr ⟩ pf = 
  subst-0 (λ z → Halt? _ z) (π₁ (π₂ (S.step-ins pf))) (go ((π₂ (π₂ (S.step-ins pf)))))

-- The erased [n] is the termination factor
-- If the machine stops, do nothing. Otherwise, step and recurse.
step-exe : ∀{@0 A₀ n} → Config-exe A₀ n → Config-exe A₀ zero
step-exe (conf-exe c (stop pf)) = conf-exe c (stop pf)
step-exe (conf-exe c (go pf)) = step-exe (conf-exe (step c) (halt-lemma (step c) (step-lemma c pf)))

result : ∀{@0 A₀} → Config-exe A₀ zero → Val A₀
result (conf-exe ⟨ ret , env , stack ∷ v , · ⟩ (stop pf)) = v

interp : ∀{@0 A₀} → (c : Config A₀) → Val A₀
interp c = result (step-exe (conf-exe c (halt-lemma c (π₂ (π₂ (Termination c))))))
