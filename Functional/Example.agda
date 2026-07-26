module Functional.Example where

open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.Nat

open import Basic
open import Context
import Functional.Syntax as S

module @0 E1 where
  open S
  open import Functional.TypeMachine.Types
  open import Functional.TypeMachine.Termination

  I : Is
  I = 
    let f = v₁ {·} {One ⇒ One} {One} in  
    let a = v₀ {· ∷ One ⇒ One} {One} in
    pushc (
      pushc (var f ⨾ var f ⨾ var f ⨾ var f ⨾ var a ⨾ app ⨾ app ⨾ app ⨾ app ⨾ ret) ⨾ 
      ret
    ) ⨾ 
    pushc (var (v₀ {·} {One}) ⨾ ret) ⨾ 
    app ⨾
    unit ⨾
    app ⨾ 
    ret
  
  I-ty : · ⊢ I ∈ · ⟶ (· ∷ One)
  I-ty = 
    Ty-⨾ 
      (Ty-pushc 
        (Ty-⨾ 
          (Ty-pushc (Ty-⨾ (Ty-var v₁) (Ty-⨾ (Ty-var v₁) (Ty-⨾ (Ty-var v₁) (Ty-⨾ (Ty-var v₁) (Ty-⨾ (Ty-var v₀) (Ty-⨾ Ty-app (Ty-⨾ Ty-app (Ty-⨾ Ty-app (Ty-⨾ Ty-app Ty-ret)))))))))) 
          Ty-ret)) 
      (Ty-⨾ (Ty-pushc (Ty-⨾ (Ty-var v₀) Ty-ret)) 
      (Ty-⨾ Ty-app (Ty-⨾ Ty-unit (Ty-⨾ Ty-app Ty-ret))))

  run : Σ Val (λ v → ⟨ I , · , · , · ⟩ ⇓ v)
  run = exec I-ty

module E2 where
  open import Functional.TypeMachine.Intrinsic

  I : Is · · (· ∷ One)
  I = pushc (
      pushc (var v₁ ⨾ var v₁ ⨾ var v₁ ⨾ var v₁ ⨾ var v₀ ⨾ app ⨾ app ⨾ app ⨾ app ⨾ ret) ⨾ 
      ret
    ) ⨾ 
    pushc (var v₀ ⨾ ret) ⨾ 
    app ⨾
    unit ⨾
    app ⨾ 
    ret 
  
  run : Val One
  run = exec I

module Factorial where
  open import Functional.TypeMachine.Intrinsic
  open import Functional.Calculus.Syntax

  I : Is · · (· ∷ Nat)
  I = 
    pushc ( 
      var v₀ ⨾
      rec 
        (lit 1 ⨾ ret) 
        -- (x, r). (suc x) * r
        (var v₀ ⨾ var v₁ ⨾ suc ⨾ mult ⨾ ret) ⨾ 
      ret 
    ) ⨾ 
    lit 5 ⨾ 
    app ⨾ 
    ret

  source : Tm · (Nat ⇒ Nat)
  source = lam (rec (lit 1) (mult (var v₀) (suc (var v₁))) (var v₀))

  target : Is · · (· ∷ Nat)
  target = compile (app source (lit 5))

  run : Val Nat
  run = exec I

{-
module Ackermann where 
  open import Functional.TypeMachine.Intrinsic
  
  Ack : (m n : ℕ) → Is · · (· ∷ Nat)
  Ack m n = 
    -- Aₘ 
    pushc (pushc (pushc( 
      -- λ f m n. (rec((λx.x+1), (_, g).(λx. f g (x+1) 1), m)) n
      var v₁ ⨾
      rec 
        (pushc (var v₀ ⨾ suc ⨾ ret) ⨾ ret) 
        (pushc (var (vs (vs (vs v₂))) ⨾ var v₁ ⨾ app ⨾ var v₀ ⨾ suc ⨾ app ⨾ lit 1 ⨾ app ⨾ ret) ⨾ ret) ⨾
      var v₀ ⨾
      app ⨾ 
      ret ) ⨾ ret) ⨾ ret
    ) ⨾

    -- The repeat function
    pushc (pushc (pushc ( 
      -- λ f n x. rec(x, (_,p).f p, n)
      var v₁ ⨾ 
      rec 
        (var v₁ ⨾ ret) 
        (var (vs (vs v₂)) ⨾ var v₀ ⨾ app ⨾ ret) ⨾ 
      ret) ⨾ ret) ⨾ ret
    ) ⨾
    app ⨾
    lit m ⨾
    app ⨾ 
    lit n ⨾ 
    app ⨾
    ret

  run : (m n : ℕ) → Exec (Ack m n)
  run m n = exec (Ack m n)

  run43 = exec (Ack 4 3)

  run-v : (m n : ℕ) → S.Val
  run-v m n = π₁ (run m n)

module Factorial2 where
  open import Functional.TermMachine.Intrinsic
  open import Functional.Calculus.Syntax
  import Functional.TermMachine.Types as T
  import Functional.Calculus.Shallow as M

  source : Tm · (Nat ⇒ Nat)
  source = lam (rec (lit 1) (mult (var v₀) (suc (var v₁))) (var v₀))

  target : Is · T.· (T.· T.∷ M.lit 120)
  target = compile (app source (lit 5))

  run : Exec target
  run = exec target

module Fib where
  open import Functional.TermMachine.Intrinsic
  open import Functional.Calculus.Syntax
  import Functional.TermMachine.Types as T
  import Functional.Calculus.Shallow as M

  source : Tm · (Nat ⇒ Nat)
  source = lam ( -- fib x = 
    rec 
      (lit 0) -- if x = 0 then 0
      (snd -- else x = suc y, compute (fib y, fib (y + 1))
        (rec 
          (pair (lit 0) (lit 1)) -- zero case: (1, 1)
          (pair (snd (var v₀)) (add (fst (var v₀)) (snd (var v₀)))) -- recursive case: (fib (y + 1), fib y + fib (y + 1))
          (var v₁)
        )
      ) 
      (var v₀)
    )
  
  fib : ℕ → Tm · Nat
  fib n = app source (lit n)

  target : Is · T.· (T.· T.∷ M.lit 55)
  target = compile (fib 10)

  run : Exec target
  run = exec target

open import Functional.TermMachine.Intrinsic
-} 
