module Basic where

open import Agda.Primitive
open import Data.Nat
open import Relation.Binary.PropositionalEquality 

infixr 5 _∘_
_∘_ : ∀{ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {C : (a : A) → B a → Set ℓ''} →
        (f : {a : A}(b : B a) → C a b) →
        (g : (a : A) → B a) →
        (a : A) → C a (g a)
(g ∘ f) x = g (f x)

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

absurd : ∀{i}{A : Set i} → ⊥ → A
absurd ()

suc-inj : ∀{m n} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

ext-⊤ : ∀{i}{A : Set i}{f g : ⊤ → A} → ({t : ⊤} → f t ≡ g t) → f ≡ g
ext-⊤ pf = cong (λ a _ → a) pf

ext-tt : ∀{i}{A : Set i}{f g : ⊤ → A} → (f tt ≡ g tt) → f ≡ g
ext-tt pf = cong (λ a _ → a) pf

absurd-0 : ∀{i}{A : Set i} → @0 ⊥ → A
absurd-0 ()

subst-0 : 
  ∀{@0 i j}{@0 A : Set i}(@0 P : A → Set j) → 
  {@0 x y : A} → @0 x ≡ y → P x → P y
subst-0 P refl x = x

