module hindley-milner where 

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

module Rules (TVar : Set) where

  data Typ (V : Set) : Set where
   tvar : V → Typ V
   _[→]_ : Typ V → Typ V → Typ V
  infixr 100 _[→]_

  _+'_ : ℕ → Set → Set
  0 +' S = S
  suc n +' S = Maybe (n +' S)

  Schema : Set → Set
  Schema V = ∃ λ n → Typ (n +' V)

  Context : Set → Set → Set
  Context V TV = V → Schema TV

  data Expr (V : Set) : Set where
    var : V → Expr V
    lam : Expr (Maybe V) → Expr V
    app : Expr V → Expr V → Expr V
    fix : Expr (Maybe V) → Expr V
    let' : Expr V → Expr (Maybe V) → Expr V

  push : ∀ {V TV} → Context V TV → Schema TV → Context (Maybe V) TV
  push c _ (just x) = c x
  push c t nothing = t

  _∷_∈_ : ∀ {V TV} → V → Schema TV → Context V TV → Set
  x ∷ σ ∈ Γ = Γ x ≡ σ

  Inst = λ (V : Set) n → Vec (Typ V) n
  
  locals : ∀ {V} → Schema V → ℕ
  locals s = proj₁ s

  bind : ∀ {A B} → Typ A → (A → Typ B) → Typ B
  bind (tvar x) f = f x
  bind (s [→] t) f =  bind s f [→] bind s f

  subs1 : ∀ {V} → Typ (Maybe V) → Typ V → Typ V
  subs1 (tvar (just v)) x = tvar v
  subs1 (tvar nothing) x = x
  subs1 (s [→] t) x =  subs1 s x [→] subs1 t x

  lift1 : ∀ {V} → Typ V → Typ (1 +' V)
  lift1 t = bind t (λ x → tvar (just x))

  liftn : ∀ {V n} → Typ V → Typ (n +' V)
  liftn {n = zero} t = t
  liftn {n = suc n} t = lift1 (liftn {n = n} t)

  subs' : ∀ {V n} → Inst V n → Typ (n +' V) → Typ V
  subs' [] t = t
  subs' {n = suc n} (x ∷ xs) t = subs' xs (subs1 t (liftn {n = n} x))

  subs : ∀ {V} → (s : Schema V) → Inst V (proj₁ s) → Typ V
  subs (_ , t) i = subs' i t

  hmm : forall {TV} m n -> Typ (m +' TV) -> Typ (m +' (n +' TV))
  hmm m n t = bind t ?

  gen1 : forall {TV} n -> Schema TV -> Schema (n +' TV)
  gen1 n (m , t) = (m , hmm m n t)

  gen : forall {V TV} n -> Context V TV -> Context V (n +' TV)
  gen n c v = gen1 n (c v)

  data _⊢_∷_ {V TV : Set} : Context V TV → Expr V → Typ TV → Set where 
    var : ∀ x {t} {σ} {Γ} inst
      → subs σ inst ≡ t
      → x ∷ σ ∈ Γ
      ---------------
      → Γ ⊢ var x ∷ t

    app : ∀ {Γ e₀ e₁ t t'}
      → Γ ⊢ e₀ ∷ t [→] t'
      → (Γ ⊢ e₁ ∷ t)
      ---------------
      → Γ ⊢ app e₀ e₁ ∷ t'
       
    lam : ∀ {Γ e t t'}
      → push Γ (0 , t) ⊢ e ∷ t'
      ---------------
      → Γ ⊢ lam e ∷ t [→] t'

    let' : forall n s t e0 e1 Γ
      -> gen n Γ ⊢ e0 ∷ s
      -> push Γ (n , s) ⊢ e1 ∷ t
      ---------------
      -> Γ ⊢ let' e0 e1 ∷ t
