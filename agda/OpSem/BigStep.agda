open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma renaming (_,_ to ⟨_,_⟩)

open import LaterPrims
open import Term
open import Substitution.Base

module OpSem.BigStep where

private variable l : Level

VPred : {l : Level} (τ : Type) → Set (lsuc l)
VPred {l = l} τ = {e : ∅ ⊢ τ} (v : Value e) (k : Nat) → Set l

⇓-pred-body : (Q : VPred {l} nat) {e : ∅ ⊢ nat} (v : Value e) (k : Nat) → Set l
⇓-pred-body Q (v-nat zero) k = Q (v-nat zero) k
⇓-pred-body Q (v-nat (suc n)) k = Q (v-nat n) k

⇓-succ-body : (Q : VPred {l} nat) {e : ∅ ⊢ nat} (v : Value e) (k : Nat) → Set l
⇓-succ-body Q (v-nat n) k = Q (v-nat (suc n)) k

⇓-ifz-body : (Q : VPred {l} τ) (t₀ t₁ : ∅ ⊢ τ) {e : ∅ ⊢ nat} (v : Value e) (k : Nat) → Set l

⇓-app-body : (Q : VPred {l} τ₂) (t : ∅ ⊢ τ₁) {f : ∅ ⊢ τ₁ ⇒ τ₂} (v : Value f) (k : Nat) → Set l

infix 5 _⇓[_]_

{-# NO_UNIVERSE_CHECK #-}
data _⇓[_]_ {l : Level} : ∅ ⊢ τ → Nat → VPred {l} τ → Set l where
    ⇓-v : {Q : VPred τ} {k : Nat} {e : ∅ ⊢ τ}
        → (v : Value e) 
        → Q v k
        → e ⇓[ k ] Q

    ⇓-pred : {Q : VPred nat} {k : Nat} {e : ∅ ⊢ nat}
           → e ⇓[ k ] ⇓-pred-body Q
           → pred e ⇓[ k ] Q

    ⇓-succ : {Q : VPred nat} {k : Nat} {e : ∅ ⊢ nat}
           → e ⇓[ k ] ⇓-succ-body Q
           → succ e ⇓[ k ] Q

    ⇓-ifz : {Q : VPred τ} {k : Nat} {e : ∅ ⊢ nat} {t₀ t₁ : ∅ ⊢ τ}
           → e ⇓[ k ] ⇓-ifz-body Q t₀ t₁
           → ifz e then t₀ else t₁ ⇓[ k ] Q

    ⇓-app : {Q : VPred τ₂} {k : Nat} {f : ∅ ⊢ τ₁ ⇒ τ₂} {t : ∅ ⊢ τ₁}
          → f ⇓[ k ] ⇓-app-body Q t
          → f ∙ t ⇓[ k ] Q

    ⇓-unfold : {Q : VPred τ} {k : Nat} {f : ∅ ⊢ τ ⇒ τ}
             → ▹ (f ∙ (Y f) ⇓[ k ] Q)
             → Y f ⇓[ suc k ] Q

⇓-ifz-body Q t₀ t₁ (v-nat zero)    k = t₀ ⇓[ k ] Q
⇓-ifz-body Q t₀ t₁ (v-nat (suc _)) k = t₁ ⇓[ k ] Q

⇓-app-body Q t (v-abs f) k = f [ t ] ⇓[ k ] Q

variable
  Q  : VPred τ
  Q𝕟 : VPred nat
