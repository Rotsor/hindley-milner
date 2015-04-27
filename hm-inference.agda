module hm-inference where

import hindley-milner
open  hindley-milner.Rules
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product

infer : ∀ {V TV} → (Γ : Context V TV) → (e : Expr V) → Dec (Σ (Schema TV) (λ s → ((i : Inst TV (proj₁ s)) → Γ ⊢ e ∷ subs s i) × ((t : Typ TV) → Γ ⊢ e ∷ t → Σ (Inst TV (proj₁ s)) (λ i → subs s i ≡ t))))
infer Γ (var x) = yes (Γ x , (λ i → var x i refl) , (λ t → λ { (var .x inst proof) → inst , proof }))
infer Γ (lam e) with infer {!push Γ (monomorphic t)!} e
... | result = {!!}
infer Γ (app e e₁) = {!!}
infer Γ (fix e) = {!!}
infer Γ (let' e e₁) with infer Γ e
infer Γ (let' e e₁) | yes p = {!!}
infer Γ (let' e e₁) | no ¬p =
  no (λ { (x , well-typed , proj₂) → {!!} })
