open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma renaming (_,_ to ⟨_,_⟩)

open import Helper
open import LaterPrims
open import Term
open import Substitution.Base

module OpSem.SmallStep where

infix 5 _→[_]_
infix 5 _⇒[_]_

data _→[_]_ {Γ : Ctx} : Γ ⊢ τ → Bool → Γ ⊢ τ → Set where
  red-app : {f f' : Γ ⊢ τ₁ ⇒ τ} {t : Γ ⊢ τ₁} {k : Bool}
          → f →[ k ] f'
          → f ∙ t →[ k ] f' ∙ t
  red-beta : {f : Γ , τ₁ ⊢ τ} {t : Γ ⊢ τ₁}
           → abs f ∙ t →[ false ] f [ t ]

  red-ifz  : {e e' : Γ ⊢ nat} {t₀ t₁ : Γ ⊢ τ} {k : Bool}
           → e →[ k ] e'
           → ifz e then t₀ else t₁ →[ k ] ifz e' then t₀ else t₁
  red-pred : {e e' : Γ ⊢ nat} {k : Bool}
           → e →[ k ] e'
           → pred e →[ k ] pred e'
  red-succ : {e e' : Γ ⊢ nat} {k : Bool}
           → e →[ k ] e'
           → succ e →[ k ] succ e'

  red-pred' : {n : Nat} → pred (# n) →[ false ] # nat-pred n
  red-succ' : {n : Nat} → succ (# n) →[ false ] # nat-succ n
  red-ifz-z : {t₀ t₁ : Γ ⊢ τ}
            → ifz # zero then t₀ else t₁ →[ false ] t₀
  red-ifz-s : {n : Nat} {t₀ t₁ : Γ ⊢ τ}
            → ifz # suc n then t₀ else t₁ →[ false ] t₁


  red-unfold : {f : Γ ⊢ τ ⇒ τ}
             → Y f →[ true ] f ∙ (Y f)

data _⇒[_]_ {Γ : Ctx} : Γ ⊢ τ → Nat → Γ ⊢ τ → Set where
  mred-refl : {e : Γ ⊢ τ}
            → e ⇒[ zero ] e

  mred-z : {e e' e'' : Γ ⊢ τ}
         → e  →[ false ] e'
         → e' ⇒[ zero  ] e''
         → e  ⇒[ zero  ] e''

  mred-s : {e e₀ e₁ e' : Γ ⊢ τ} {k : Nat}
         → e  ⇒[ zero  ] e₀
         → e₀ →[ true  ] e₁
         → e₁ ⇒[ k     ] e'
         → e  ⇒[ suc k ] e'

