open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Cubical.Path

open import Helper using (nat-pred; nat-succ)
open import LaterPrims
open import Term
open import Denotation.LaterAlgebra

module Denotation.Interpretation where

⟦_⟧t : Type → Set
⟦ nat ⟧t = 𝓛 Nat
⟦ σ ⇒ τ ⟧t = ⟦ σ ⟧t → ⟦ τ ⟧t

▹alg-⟦_⟧t : (τ : Type) → ▹algebra ⟦ τ ⟧t
▹alg-⟦ nat ⟧t = ▹alg-free
▹alg-⟦ σ ⇒ τ ⟧t = ▹alg-fun ▹alg-⟦ τ ⟧t

▹alg' : ▹algebra ⟦ τ ⟧t
▹alg' = ▹alg-⟦ _ ⟧t

θ' : ▹ ⟦ τ ⟧t → ⟦ τ ⟧t
θ' = let pack θ = ▹alg-⟦ _ ⟧t in θ

δ' : ⟦ τ ⟧t → ⟦ τ ⟧t
δ' x = θ' (next x)

data ⟦_⟧c : Ctx → Set where
  ∅ : ⟦ ∅ ⟧c
  _∷_ : ⟦ τ ⟧t → ⟦ Γ ⟧c → ⟦ Γ , τ ⟧c

variable
    γ : ⟦ Γ ⟧c
    α : ⟦ τ ⟧t

infixl 9 _⟨_⟩ᵉ

_⟨_⟩ᵉ : ⟦ Γ ⟧c → Γ ∋ τ → ⟦ τ ⟧t
(α ∷ γ) ⟨ Z ⟩ᵉ = α
(σ ∷ γ) ⟨ S x ⟩ᵉ = γ ⟨ x ⟩ᵉ

nat-ifz : ∀ {A : Set} (x y : A) (n : Nat) → A
nat-ifz t0 t1 zero = t0
nat-ifz t0 t1 (suc n) = t1

⟦_⟧ : Γ ⊢ τ → ⟦ Γ ⟧c → ⟦ τ ⟧t
⟦ var x ⟧ γ = γ ⟨ x ⟩ᵉ
⟦ f ∙ t ⟧ γ = ⟦ f ⟧ γ (⟦ t ⟧ γ)
⟦ abs t ⟧ γ = λ α → ⟦ t ⟧ (α ∷ γ)
⟦ # n ⟧ γ = now n
⟦ pred t ⟧ γ = 𝓛-map nat-pred (⟦ t ⟧ γ)
⟦ succ t ⟧ γ = 𝓛-map nat-succ (⟦ t ⟧ γ)
⟦ ifz e then t0 else t1 ⟧ γ = map-ext ▹alg' (nat-ifz (⟦ t0 ⟧ γ) (⟦ t1 ⟧ γ)) (⟦ e ⟧ γ)
⟦ Y f ⟧ γ = gfix (λ x → θ' (next (⟦ f ⟧ γ) ⊛ x))
