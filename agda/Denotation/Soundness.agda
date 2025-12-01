open import Cubical.Foundations.Prelude hiding (Type; _,_; _∙_; cong; cong₂; cong₃)

open import Helper
open import LaterPrims
open import Term
open import Denotation.LaterAlgebra
open import Denotation.Interpretation

module Denotation.Soundness where

Y-delay : (f : Γ ⊢ τ ⇒ τ)
        → ⟦ Y f ⟧ γ ≡ δ' (⟦ f ∙ (Y f) ⟧ γ)
Y-delay {γ = γ} f =
    ⟦ Y f ⟧ γ
        ≡⟨⟩
    gfix (λ x → θ' (next (⟦ f ⟧ γ) ⊛ x))
        ≡⟨ (gfix-unfold λ { x → θ' (next (⟦ f ⟧ γ) ⊛ x) }) ⟩
    θ' (next (⟦ f ⟧ γ) ⊛ next (⟦ Y f ⟧ γ))
        ≡⟨⟩
    θ' (next ((⟦ f ⟧ γ) (⟦ Y f ⟧ γ)))
        ≡⟨⟩
    δ' (⟦ f ∙ (Y f) ⟧ γ) ∎

ifz-delay : (n n' : Γ ⊢ nat) (t0 t1 : Γ ⊢ τ)
          → ⟦ n ⟧ γ ≡ δ' {nat} (⟦ n' ⟧ γ)
          → ⟦ ifz n then t0 else t1 ⟧ γ ≡ δ' (⟦ ifz n' then t0 else t1 ⟧ γ)
ifz-delay {γ = γ} n n' t0 t1 eq = {! !}
