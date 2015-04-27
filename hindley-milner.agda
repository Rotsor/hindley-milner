module hindley-milner where 

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

module Rules where

  data Typ (V : Set) : Set where
   tvar : V → Typ V
   _[→]_ : Typ V → Typ V → Typ V
  infixr 100 _[→]_

  _+'_ : ℕ → Set → Set
  n +' S = Fin n ⊎ S

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
  push c t = maybe c t

  _∷_∈_ : ∀ {V TV} → V → Schema TV → Context V TV → Set
  x ∷ σ ∈ Γ = Γ x ≡ σ

  Inst = λ (V : Set) n → (Fin n → Typ V)

  bind : ∀ {A B} → Typ A → (A → Typ B) → Typ B
  bind (tvar x) f = f x
  bind (s [→] t) f =  bind s f [→] bind t f

  mapT : ∀ {A B} → (A → B) → Typ A → Typ B
  mapT f t = bind t (λ x → tvar (f x))

  lift : ∀ {V} n → Typ V → Typ (n +' V)
  lift n t = bind t (λ v → tvar (inj₂ v))

  subs' : ∀ {V n} → Inst V n → Typ (n +' V) → Typ V
  subs' vec t = bind t (λ {
    (inj₁ i) → vec i ;
    (inj₂ v) → tvar v })

  subs : ∀ {V} → (s : Schema V) → Inst V (proj₁ s) → Typ V
  subs (_ , t) i = subs' i t

  hmm : forall {TV} m n -> Typ (m +' TV) -> Typ (m +' (n +' TV))
  hmm m n t = bind t (λ { (inj₁ x) → tvar (inj₁ x) ; (inj₂ y) → tvar (inj₂ (inj₂ y)) })

  gen1 : forall {TV} n -> Schema TV -> Schema (n +' TV)
  gen1 n (m , t) = (m , hmm m n t)

  gen : forall {V TV} n -> Context V TV -> Context V (n +' TV)
  gen n c v = gen1 n (c v)

  monomorphic : ∀ {V} → Typ V → Schema V
  monomorphic t = (0 , bind t (λ { x → tvar (inj₂ x)  }))

  data _⊢_∷_ {V TV : Set} : Context V TV → Expr V → Typ TV → Set where 
    var : ∀ x {t} {Γ} inst
      → subs (Γ x) inst ≡ t
      ---------------
      → Γ ⊢ var x ∷ t

    app : ∀ {Γ e₀ e₁ t t'}
      → Γ ⊢ e₀ ∷ t [→] t'
      → (Γ ⊢ e₁ ∷ t)
      ---------------
      → Γ ⊢ app e₀ e₁ ∷ t'
       
    lam : ∀ {Γ e t t'}
      → push Γ (monomorphic t) ⊢ e ∷ t'
      ---------------
      → Γ ⊢ lam e ∷ t [→] t'

    let' : ∀ n {s t e₀ e₁ Γ}
      -> gen n Γ ⊢ e₀ ∷ s
      -> push Γ (n , s) ⊢ e₁ ∷ t
      ---------------
      -> Γ ⊢ let' e₀ e₁ ∷ t

    fix :
      ∀ {t Γ e}
      → push Γ (monomorphic t) ⊢ e ∷ t
      → Γ ⊢ fix e ∷ t

    poly-fix :
      ∀ n {t : Typ (n +' TV)} {Γ} {e}
      → gen n (push Γ (n , t)) ⊢ e ∷ t
      → ∀ inst
      → Γ ⊢ fix e ∷ (subs' inst t)

    -- [fix g E]
    -- [let g = E in g]
    let-rec :
      ∀ n {t₀ t₁} {Γ} {e₀ e₁}
      → let Γ' = push Γ (n , t₀) in
      gen n Γ' ⊢ e₀ ∷ t₀
      → Γ' ⊢ e₁ ∷ t₁
      → Γ ⊢ let' (fix e₀) e₁ ∷ t₁

  _⊢'_∷_ : ∀ {V TV : Set} → Context V TV → Expr V → Schema TV → Set
  Γ ⊢' e ∷ (n , t) = gen n Γ ⊢ e ∷ t

  module Examples where
    open import Data.Empty
    truly-empty : Context ⊥ ⊥
    truly-empty ()

    id-well-typed : truly-empty ⊢' (lam (var nothing)) ∷ (2 , tvar (inj₁ (suc zero)) [→] tvar (inj₁ (suc zero)))
    id-well-typed = lam (var nothing (λ ()) refl)

    open import Data.Bool
    data Constant : Set where
      nat : ℕ → Constant
      bool : Bool → Constant
      make-nat-with-bool : Constant

    data BaseType : Set where
      nat : BaseType
      bool : BaseType
      nat-with-bool : BaseType

    with-base-types : Context Constant BaseType
    with-base-types (nat n) = 0 , tvar (inj₂ nat)
    with-base-types (bool x) = 0 , tvar (inj₂ bool)
    with-base-types make-nat-with-bool = 0 , tvar (inj₂ nat) [→] (tvar (inj₂ bool) [→] tvar (inj₂ nat-with-bool))

    term : Expr Constant
    term = let' (lam (var nothing)) (app (app (var (just make-nat-with-bool)) (app (var nothing) (var (just (nat 1))))) (app (var nothing) (var (just (bool true)))))

    well-typed-term : with-base-types ⊢ term ∷ tvar nat-with-bool
    well-typed-term =
      let' 1 (lam
        {t = tvar (inj₁ zero)}
        (var nothing (λ ()) refl))
        (app (
          app (var (just make-nat-with-bool) (λ ()) refl)
         (app (var nothing (λ _ → tvar nat) refl) (var (just (nat (suc zero))) (λ ()) refl))) (app (var nothing (λ _ → tvar bool) refl) (var (just (bool true)) (λ ()) refl)))

    term-fix : Expr Constant
    term-fix = let' (fix (lam (var nothing))) (app (app (var (just make-nat-with-bool)) (app (var nothing) (var (just (nat 1))))) (app (var nothing) (var (just (bool true)))))

    well-typed-term-fix : with-base-types ⊢ term-fix ∷ tvar nat-with-bool
    well-typed-term-fix =
      let-rec 1 (lam
        {t = tvar (inj₁ zero)}
        {t' = tvar (inj₁ zero)}
        (var nothing (λ ()) refl))
        (app {t = tvar bool} {t' = tvar nat-with-bool} (
          app {t = tvar nat} {t' = tvar bool [→] tvar nat-with-bool}  (var (just make-nat-with-bool) (λ ()) refl)
         (app (var nothing (λ _ → tvar nat) refl) (var (just (nat (suc zero))) (λ ()) refl))) (app (var nothing (λ _ → tvar bool) refl) (var (just (bool true)) (λ ()) refl)))

  


{-  TVar : ∀ {V TV} → Context V TV → Set
  TVar {_} {TV} _ = TV

  gen-push-commute :
    ∀ {T TV} m n (G : Context T TV) t →
     push (gen n G) (m , hmm m n t)
     ≗ gen n (push G (m , t))
  gen-push-commute m n G t (just x) = refl
  gen-push-commute m n G t nothing = refl

  pw-sym : ∀ {A B : Set} → {f g : A → B} →  f ≗ g → g ≗ f
  pw-sym eq x = sym (eq x)

  subst-context : ∀ {T} {TV} (Γ₁ Γ₂ : Context T TV)
    → ∀ e t → Γ₁ ≗ Γ₂
    → Γ₁ ⊢ e ∷ t → Γ₂ ⊢ e ∷ t
  subst-context {T} {TV} Γ₁ Γ₂ .(var x) t eq (var x inst x₁) rewrite eq x =
    var x inst x₁
  subst-context Γ₁ Γ₂ ._ t eq (app proof proof₁) =
    app (subst-context Γ₁ Γ₂ _ (_ [→] t) eq proof)
      (subst-context Γ₁ Γ₂ _ _ eq proof₁)
  subst-context Γ₁ Γ₂ ._ ._ eq (lam proof) = lam (subst-context _ _ _ _ {!!} proof)
  subst-context Γ₁ Γ₂ ._ t eq (let' n proof proof₁) = {!!}
  subst-context Γ₁ Γ₂ ._ t eq (fix proof) = {!!}
  subst-context Γ₁ Γ₂ ._ ._ eq (poly-fix n proof inst) = {!!}
  subst-context Γ₁ Γ₂ ._ t eq (let-rec n proof proof₁) = {!!}

  cong-gen :
    ∀ {T} {TV} {x y : Context T TV} n
    → x ≗ y → gen n x ≗ gen n y
  cong-gen n eq x = cong (gen1 n) (eq x)

  theoremG :
   ∀ {V TV} n k (Γ : Context V TV) t₀ e₀ →
    gen n Γ ⊢ e₀ ∷ t₀ →
    gen n (gen k Γ) ⊢ e₀ ∷ hmm n k t₀
  theoremG n k G t .(var x) (var x inst x₁) = var x (λ v → hmm n k (inst v)) {!!}
  theoremG n k G t ._ (app proof proof₁) = {!!}
  theoremG n k G ._ ._ (lam proof) = {!!}
  theoremG n k G t ._ (let' n₁ proof proof₁) = {!!}
  theoremG n k G t ._ (fix proof) = {!!}
  theoremG n k G ._ ._ (poly-fix n₁ proof inst) = {!!}
  theoremG n k G t ._ (let-rec n₁ proof proof₁) = {!!}

  theorem :
   ∀ {V TV} n (Γ : Context V TV) t₀ e₀ →
    gen n (push Γ (n , t₀))
     ⊢ e₀ ∷ t₀ →
     
    gen n (push (gen n Γ) (n , hmm n n t₀))
     ⊢ e₀ ∷ hmm n n t₀
  theorem n G t0 e0 proof =
    subst-context _ _ _ _ (cong-gen {x = (gen n (push G (n , t0)))} {y =  (push (gen n G) (n , hmm n n t0))} n
      ( pw-sym (gen-push-commute n n G t0) )) (theoremG n n (push G (n , t0)) t0 e0 proof)

  swap-let-rec-and-let-and-fix :
    ∀ {V TV} (Γ : Context V TV) e t → Γ ⊢ e ∷ t → Γ ⊢ e ∷ t
  swap-let-rec-and-let-and-fix Γ .(var x) t (var x inst x₂) = {!!}
  swap-let-rec-and-let-and-fix Γ ._ t (app proof proof₁) = {!!}
  swap-let-rec-and-let-and-fix Γ ._ ._ (lam proof) = {!!}
  swap-let-rec-and-let-and-fix Γ ._ t (let' n proof proof₁) = {!!}
  swap-let-rec-and-let-and-fix Γ ._ t (fix proof) = {!!}
  swap-let-rec-and-let-and-fix Γ ._ ._ (poly-fix n proof inst) = {!!}
  swap-let-rec-and-let-and-fix Γ ._ t (let-rec n {t₀} .{t} {e₀ = e₀} {e₁} proof₀ proof₁) = result where
     {-
       [Γ](
        letrec
         f = [Γ₂o](e₀ : t₀)
        in 
         [Γ₃o] (e₁ : t))
     -}

     {-
       [Γ](
        let
         x = [Γ₁](fix f [Γ₂](e₀))
        in 
         [Γ₃] e₁)
     -}
     Γ₁ = gen n Γ
     Γ₃ = push Γ (n , t₀)
     Γ₂ = gen n (push Γ₁ (n , hmm n n t₀))
     Γ₂o = gen n (push Γ (n , t₀))
--     type-of-f-in-scope-of-let : Typ (TVar )
     fix-expr : Γ₂ ⊢ e₀ ∷ hmm n n t₀
     fix-expr = {! Γ-inside-fix!}
     result = let' n {e₀ = fix e₀} {e₁} (
       poly-fix n {t = lift n t₀} {Γ = Γ₁} {e = e₀} {! proof₀!} (λ x → tvar (inj₁ x)))
       {!proof₁!} -- proof₁
-}
