open import Cubical.Foundations.Prelude hiding (Type; _,_; _∙_; cong; cong₂; cong₃)

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

open import Helper
open import LaterPrims
open import Term
open import Renaming.Base
open import Substitution.Base
open import Denotation.LaterAlgebra
open import Denotation.Interpretation
open import Denotation.RenSub
open import OpSem.SmallStep

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


sound→[z] : (e e' : Γ ⊢ τ) → e →[ false ] e' → ⟦ e ⟧ γ ≡ ⟦ e' ⟧ γ
sound→[z] {γ = γ} (f ∙ t) .(f' ∙ t) (red-app {f' = f'} f→f') = cong (λ [f] → [f] (⟦ t ⟧ γ)) (sound→[z] f f' f→f')
sound→[z] {γ = γ} (abs f ∙ t) e' red-beta =
    ⟦ abs f ∙ t ⟧ γ
        ≡⟨⟩
    (⟦ abs f ⟧ γ) (⟦ t ⟧ γ)
        ≡⟨⟩
    ⟦ f ⟧ (⟦ t ⟧ γ ∷ γ)
        ≡⟨ cong (λ [γ] → ⟦ f ⟧ (⟦ t ⟧ γ ∷ [γ])) (sym subst-idᶜ⟪ γ ⟫ˢ) ⟩
    ⟦ f ⟧ (⟦ t ⟧ γ ∷ idˢ _ ᶜ⟪ γ ⟫ˢ)
        ≡⟨⟩
    ⟦ f ⟧ ((t ∷ idˢ _) ᶜ⟪ γ ⟫ˢ)
        ≡⟨ subst-⟦ f ⟧ (t ∷ idˢ _) γ ⟩
    ⟦ (t ∷ idˢ _) ⟪ f ⟫ˢ ⟧ γ
        ≡⟨⟩
    ⟦ f [ t ] ⟧ γ ∎
sound→[z] (pred e) (pred e') (red-pred e→e') = cong (𝓛-map nat-pred) (sound→[z] e e' e→e')
sound→[z] (pred (# zero)) (# zero) red-pred' = refl
sound→[z] (pred (# suc n)) (# n) red-pred' = refl
sound→[z] (succ e) (succ e') (red-succ e→e') = cong (𝓛-map nat-succ) (sound→[z] e e' e→e')
sound→[z] (succ (# n)) e' red-succ' = refl
sound→[z] {γ = γ} (ifz e then t₀ else t₁) (ifz e' then t₀ else t₁) (red-ifz e→e') = cong (map-ext _ (nat-ifz _ _)) (sound→[z] e e' e→e')
sound→[z] {γ = γ} (ifz (# zero) then t₀ else t₁) t₀ red-ifz-z =
    ⟦ ifz # zero then t₀ else t₁ ⟧ γ
        ≡⟨⟩
    map-ext ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ)) (now zero)
        ≡⟨⟩
    gfix (map-ext-body ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ))) (now zero)
        ≡⟨ gfix-unfold (map-ext-body ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ))) ≡$ now zero ⟩
    ⟦ t₀ ⟧ γ ∎
sound→[z] {γ = γ} (ifz (# suc _) then t₀ else t₁) e' red-ifz-s =
    ⟦ ifz (# suc _) then t₀ else t₁ ⟧ γ
        ≡⟨⟩
    map-ext ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ)) (now (suc _))
        ≡⟨⟩
    gfix (map-ext-body ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ))) (now (suc _))
        ≡⟨ gfix-unfold (map-ext-body ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ))) ≡$ now (suc _) ⟩
    ⟦ t₁ ⟧ γ ∎


sound→[s] : (e e' : Γ ⊢ τ) → e →[ true ] e' → ⟦ e ⟧ γ ≡ δ' (⟦ e' ⟧ γ)
sound→[s] {γ = γ} (f ∙ t) (f' ∙ t) (red-app f→f') =
    ⟦ f ∙ t ⟧ γ
        ≡⟨⟩
    (⟦ f ⟧ γ) (⟦ t ⟧ γ)
        ≡⟨ sound→[s] f f' f→f' ≡$ ⟦ t ⟧ γ ⟩
    (δ' (⟦ f' ⟧ γ)) (⟦ t ⟧ γ)
        ≡⟨⟩
    δ' (⟦ f' ∙ t ⟧ γ) ∎
sound→[s] {γ = γ} (pred e) (pred e') (red-pred e→e') =
    ⟦ pred e ⟧ γ
        ≡⟨⟩
    𝓛-map nat-pred (⟦ e ⟧ γ)
        ≡⟨ cong (𝓛-map nat-pred) (sound→[s] e e' e→e') ⟩
    𝓛-map nat-pred (δ' {nat} (⟦ e' ⟧ γ))
        ≡⟨⟩
    δ' {nat} (⟦ pred e' ⟧ γ) ∎
sound→[s] {γ = γ} (succ e) (succ e') (red-succ e→e') =
    ⟦ succ e ⟧ γ
        ≡⟨⟩
    𝓛-map nat-succ (⟦ e ⟧ γ)
        ≡⟨ cong (𝓛-map nat-succ) (sound→[s] e e' e→e') ⟩
    𝓛-map nat-succ (δ' {nat} (⟦ e' ⟧ γ))
        ≡⟨⟩
    δ' {nat} (⟦ succ e' ⟧ γ) ∎
sound→[s] {γ = γ} (ifz e then t₀ else t₁) (ifz e' then t₀ else t₁) (red-ifz e→e')
    = ifz-delay {n = e} {n' = e'} {t₀ = t₀} {t₁ = t₁} (sound→[s] e e' e→e')
sound→[s] {γ = γ} (Y f) (f ∙ (Y f)) red-unfold = Y-delay f



δ'[_] : Nat → ⟦ τ ⟧t → ⟦ τ ⟧t
δ'[ zero ] x = x
δ'[ suc n ] x = δ' (δ'[ n ] x)


soundness : (k : Nat) (e e' : Γ ⊢ τ)
          → e ⇒[ k ] e'
          → ⟦ e ⟧ γ ≡ δ'[ k ] (⟦ e' ⟧ γ)
soundness zero e e mred-refl = refl
soundness {γ = γ} k e e'' (mred-z {e' = e'} e→e' e'⇒e'') =
    ⟦ e ⟧ γ
        ≡⟨ sound→[z] e e' e→e' ⟩
    ⟦ e' ⟧ γ
        ≡⟨ soundness zero e' e'' e'⇒e'' ⟩
    ⟦ e'' ⟧ γ ∎
soundness {γ = γ} (suc k) e e' (mred-s {e₀ = e₀} {e₁ = e₁} e⇒e₀ e₀→e₁ e₁⇒e') =
    ⟦ e ⟧ γ
        ≡⟨ soundness zero e e₀ e⇒e₀ ⟩
    ⟦ e₀ ⟧ γ
        ≡⟨ sound→[s] e₀ e₁ e₀→e₁ ⟩
    δ' (⟦ e₁ ⟧ γ)
        ≡⟨ cong δ' (soundness k e₁ e' e₁⇒e') ⟩
    δ' (δ'[ k ] (⟦ e' ⟧ γ))
        ≡⟨⟩
    δ'[ suc k ] (⟦ e' ⟧ γ) ∎
