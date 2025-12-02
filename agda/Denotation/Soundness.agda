open import Cubical.Foundations.Prelude hiding (Type; _,_; _∙_; cong; cong₂; cong₃)

open import Agda.Builtin.Nat

open import Helper
open import LaterPrims
open import Term
open import Renaming.Base
open import Denotation.LaterAlgebra
open import Denotation.Interpretation
open import Denotation.RenSub

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

ifz-abs-future : (t₀ t₁ : Γ ⊢ τ) (r : ▹ 𝓛 Nat)
               → let M = suc-renaming (idᴿ _) ⟪ t₀ ⟫
                     N = suc-renaming (idᴿ _) ⟪ t₁ ⟫
                  in ⟦ abs (ifz var Z then M else N) ⟧ γ (future r)
                   ≡ θ' (next (⟦ abs (ifz var Z then M else N) ⟧ γ) ⊛ r)
ifz-abs-future {γ = γ} t₀ t₁ r =
    ⟦ abs (ifz var Z then M else N) ⟧ γ (future r)
        ≡⟨⟩
    ⟦ ifz var Z then M else N ⟧ (future r ∷ γ)
        ≡⟨⟩
    map-ext ▹alg' (nat-ifz (⟦ M ⟧ (future r ∷ γ)) (⟦ N ⟧ (future r ∷ γ))) (future r)
        ≡⟨ cong₂ (λ [M] [N] → map-ext ▹alg' (nat-ifz [M] [N]) (future r))
                 (suc-rename-idᴿ⟦ t₀ ⟧ γ (future r))
                 (suc-rename-idᴿ⟦ t₁ ⟧ γ (future r)) ⟩
    map-ext ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ)) (future r)
        ≡⟨⟩
    gfix (map-ext-body ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ))) (future r)
        ≡⟨ gfix-unfold (map-ext-body ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ))) ≡$ future r ⟩
    θ' (next (λ α → map-ext ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ)) α) ⊛ r)
        ≡⟨ cong (λ [f] → θ' ((next [f]) ⊛ r))
                (funExt (λ α → cong₂ (λ [M] [N] → map-ext ▹alg' (nat-ifz [M] [N]) α)
                               (sym (suc-rename-idᴿ⟦ t₀ ⟧ γ α))
                               (sym (suc-rename-idᴿ⟦ t₁ ⟧ γ α)))) ⟩
    θ' (next (λ α → map-ext ▹alg' (nat-ifz (⟦ M ⟧ (α ∷ γ)) (⟦ N ⟧ (α ∷ γ))) α) ⊛ r)
        ≡⟨⟩
    θ' (next (λ α → ⟦ ifz var Z then M else N ⟧ (α ∷ γ)) ⊛ r)
        ≡⟨⟩
    θ' (next (⟦ abs (ifz var Z then M else N) ⟧ γ) ⊛ r) ∎
  where
    M = suc-renaming (idᴿ _) ⟪ t₀ ⟫
    N = suc-renaming (idᴿ _) ⟪ t₁ ⟫


ifz-factor : (e : Γ ⊢ nat) (t₀ t₁ : Γ ⊢ τ)
           → let M = suc-renaming (idᴿ _) ⟪ t₀ ⟫
                 N = suc-renaming (idᴿ _) ⟪ t₁ ⟫
             in ⟦ ifz e then t₀ else t₁ ⟧ γ
              ≡ ⟦ abs (ifz var Z then M else N) ⟧ γ (⟦ e ⟧ γ)
ifz-factor {γ = γ} e t₀ t₁ =
    ⟦ ifz e then t₀ else t₁ ⟧ γ
        ≡⟨⟩
    map-ext ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ)) (⟦ e ⟧ γ)
        ≡⟨ cong₂ (λ [M] [N] → map-ext ▹alg' (nat-ifz [M] [N]) (⟦ e ⟧ γ))
                 (sym (suc-rename-idᴿ⟦ t₀ ⟧ γ (⟦ e ⟧ γ)))
                 (sym (suc-rename-idᴿ⟦ t₁ ⟧ γ (⟦ e ⟧ γ))) ⟩
    map-ext ▹alg' (nat-ifz (⟦ M ⟧ (⟦ e ⟧ γ ∷ γ)) (⟦ N ⟧ (⟦ e ⟧ γ ∷ γ))) (⟦ e ⟧ γ)
        ≡⟨⟩
    ⟦ ifz var Z then M else N ⟧ (⟦ e ⟧ γ ∷ γ)
        ≡⟨⟩
    ⟦ abs (ifz var Z then M else N) ⟧ γ (⟦ e ⟧ γ) ∎
  where
    M = suc-renaming (idᴿ _) ⟪ t₀ ⟫
    N = suc-renaming (idᴿ _) ⟪ t₁ ⟫


ifz-delay : {n n' : Γ ⊢ nat} {t₀ t₁ : Γ ⊢ τ}
          → ⟦ n ⟧ γ ≡ δ' {nat} (⟦ n' ⟧ γ)
          → ⟦ ifz n then t₀ else t₁ ⟧ γ ≡ δ' (⟦ ifz n' then t₀ else t₁ ⟧ γ)
ifz-delay {γ = γ} {n} {n'} {t₀} {t₁} eq =
    ⟦ ifz n then t₀ else t₁ ⟧ γ
        ≡⟨ ifz-factor n t₀ t₁ ⟩
    ⟦ abs (ifz var Z then M else N) ⟧ γ (⟦ n ⟧ γ)
        ≡⟨ cong (⟦ abs (ifz var Z then M else N) ⟧ γ) eq ⟩
    ⟦ abs (ifz var Z then M else N) ⟧ γ (δ' {nat} (⟦ n' ⟧ γ))
        ≡⟨ helper ⟩
    δ' (⟦ abs (ifz (var Z) then M else N) ⟧ γ (⟦ n' ⟧ γ))
        ≡⟨ cong δ' (sym (ifz-factor n' t₀ t₁)) ⟩
    δ' (⟦ ifz n' then t₀ else t₁ ⟧ γ) ∎
  where
    M = suc-renaming (idᴿ _) ⟪ t₀ ⟫
    N = suc-renaming (idᴿ _) ⟪ t₁ ⟫

    helper : {α : 𝓛 Nat} → ⟦ abs (ifz var Z then M else N) ⟧ γ (δ' {nat} α)
                         ≡ δ' (⟦ ifz var Z then M else N ⟧ (α ∷ γ))
    helper {α} =
        ⟦ abs (ifz var Z then M else N) ⟧ γ (δ' {nat} α)
            ≡⟨⟩
        ⟦ abs (ifz var Z then M else N) ⟧ γ (future (next α))
            ≡⟨ ifz-abs-future t₀ t₁ (next α) ⟩
        θ' (next (⟦ abs (ifz var Z then M else N) ⟧ γ) ⊛ (next α))
            ≡⟨⟩
        θ' (next (⟦ abs (ifz var Z then M else N) ⟧ γ α))
            ≡⟨⟩
        θ' (next (⟦ ifz var Z then M else N ⟧ (α ∷ γ)))
            ≡⟨⟩
        δ' (⟦ ifz var Z then M else N ⟧ (α ∷ γ)) ∎

