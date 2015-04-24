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
  
--  data [_:=_]_≡_ : Typ → TVar → Typ → Set where

  locals : ∀ {V} → Schema V → ℕ
  locals s = proj₁ s

  bind : ∀ {A B} → Typ A → (A → Typ B) → Typ B
  bind (tvar x) f = f x
  bind (s [→] t) f =  bind s f [→] bind s f

  subst1 : ∀ {V} → Typ (Maybe V) → Typ V → Typ V
  subst1 (tvar (just v)) x = tvar v
  subst1 (tvar nothing) x = x
  subst1 (s [→] t) x =  subst1 s x [→] subst1 t x

  lift1 : ∀ {V} → Typ V → Typ (1 +' V)
  lift1 t = bind t (λ x → tvar (just x))

{- 
foldr : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → A → B n → B (suc n)) →
        B zero →
        Vec A m → B m


foldl : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → B n → A → B (suc n)) →
        B zero →
        Vec A m → B m
-}
{-  subs : ∀ {V n} → Inst V n → Typ (n +' V) → Typ V
  subs {V} i = proj₁ (
    Data.Vec.foldr (λ m → (Typ (m +' V) → Typ V) × (Typ V → Typ (m +' V)) )
    ( λ { x (sub , lift) → (λ t → sub (subst1 t (lift x))) , (λ x → lift1 (lift x)) })
    ((λ x → x) , (λ x → x)) i) -}

  liftn : ∀ {V n} → Typ V → Typ (n +' V)
  liftn {n = zero} t = t
  liftn {n = suc n} t = lift1 (liftn {n = n} t)

  subs' : ∀ {V n} → Inst V n → Typ (n +' V) → Typ V
  subs' [] t = t
  subs' {n = suc n} (x ∷ xs) t = subs' xs (subst1 t (liftn {n = n} x))

  subs : ∀ {V} → (s : Schema V) → Inst V (proj₁ s) → Typ V
  subs (_ , t) i = subs' i t

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
