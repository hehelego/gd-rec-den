open import Cubical.Foundations.Prelude hiding (Type; _,_; _∙_; cong; cong₂; cong₃)

open import Agda.Builtin.Sigma renaming (_,_ to ⟨_,_⟩ₛ)
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

open import Helper
open import LaterPrims
open import Term
open import Renaming.Base
open import Substitution.Base
open import OpSem.SmallStep
open import Denotation.LaterAlgebra
open import Denotation.Interpretation
open import Denotation.RenSub
open import Denotation.Soundness


module Denotation.Adequacy where

-- TODO: check if this definition works
▹U : ▹ Set → Set
▹U ▹A = ∀ (@tick x : Tick) → ▹A x

LR : Γ ⊢ τ → ⟦ τ ⟧t → Set
LR {τ = nat} = gfix λ { ▹LR e (now n) → e ⇒[ zero ] # n
                      ; ▹LR e (future r) → ∃₂ (λ e₀ e₁
                                         → (e ⇒[ zero ] e₀)
                                         × (e₀ →[ true ] e₁)
                                         × ▹U (▹LR ⊛ next e₁ ⊛ r)) }
LR {τ = τ ⇒ σ} f φ = ∀ {t α} → LR t α → LR (f ∙ t) (φ α)

▹LR : ▹ (Γ ⊢ τ) → ▹ ⟦ τ ⟧t → Set
▹LR e α = ▹U (next LR ⊛ e ⊛ α)


LR-unfoldη : {e : Γ ⊢ nat} {n : Nat} → LR e (now n) → e ⇒[ zero ] # n
LR-unfoldη {e = e} {n = n} = transport (gfix-unfold _ ≡$ e ≡$ (now n))

LR-unfoldθ : {e : Γ ⊢ nat} {α : ▹ ⟦ nat ⟧t} → LR e (θ' α)
           → ∃₂ (λ e₀ e₁ → (e ⇒[ zero ] e₀) × (e₀ →[ true ] e₁) × ▹LR (next e₁) α)
LR-unfoldθ {e = e} {α = α} = transport (gfix-unfold _ ≡$ e ≡$ (θ' α))

LR-foldη : {e : Γ ⊢ nat} {n : Nat} → e ⇒[ zero ] # n → LR e (now n)
LR-foldη {e = e} {n = n} = transport (sym (gfix-unfold _ ≡$ e ≡$ (now n)))

LR-foldθ : {e : Γ ⊢ nat} {α : ▹ ⟦ nat ⟧t}
         → ∃₂ (λ e₀ e₁ → (e ⇒[ zero ] e₀) × (e₀ →[ true ] e₁) × ▹LR (next e₁) α)
         → LR e (θ' α)
LR-foldθ {e = e} {α = α} = transport (sym (gfix-unfold _ ≡$ e ≡$ (θ' α)))


LR⊛ : {f : Γ ⊢ τ₁ ⇒ τ₂} {φ : ▹ ⟦ τ₁ ⇒ τ₂ ⟧t}
    → {t : Γ ⊢ τ₁} {α : ▹ ⟦ τ₁ ⟧t}
    → ▹LR (next f) φ
    → ▹LR (next t) α
    → ▹LR (next (f ∙ t)) (φ ⊛ α)
LR⊛ f~φ t~α κ = f~φ κ (t~α κ)


LR→[s]θ : (e e' : Γ ⊢ τ) → e →[ true ] e'
        → (α : ▹ ⟦ τ ⟧t)
        → ▹LR (next e') α
        → LR e (θ' α)
LR→[s]θ {τ = nat} e e' e→e' α ▹R = LR-foldθ ⟨ pair e e' , pair mred-refl (pair e→e' ▹R) ⟩ₛ
LR→[s]θ {τ = τ ⇒ σ} f f' f→f' φ next[f]▹~φ {t} {α} t~α = LR→[s]θ {τ = σ}
                                                         (f ∙ t) (f' ∙ t) (red-app f→f')
                                                         (φ ⊛ next α)
                                                         (LR⊛ next[f]▹~φ (next t~α))

-- TODO: block on a lemma demonstrating that small-step is deterministic,
-- which enables one to drop the first step of a multi-step reduction
LR→[z]LR : (e e' : Γ ⊢ τ) → e →[ false ] e'
         → (α : ⟦ τ ⟧t)
         → LR e  α
         → LR e' α
LR→[z]LR {τ = nat} e e' e→e' (now n) e~α =
  let e⇒[z]n = LR-unfoldη e~α -- TODO: small-step is deterministic, drop the first-step of this multi-step reduction
   in LR-foldη ?
LR→[z]LR {τ = nat} e e' e→e' (future r) e~r =
  let q = LR-unfoldθ e~r 
   in LR-foldθ ?
LR→[z]LR {τ = τ ⇒ σ} f f' f→f' φ f~φ {t} {α} t~α = LR→[z]LR {τ = σ}
                                                   (f ∙ t) (f' ∙ t) (red-app f→f')
                                                   (φ α)
                                                   (f~φ t~α)

LR-σ~γ : Subst Γ ∅ → ⟦ Γ ⟧c → Set
LR-σ~γ ∅ ∅ = ⊤
LR-σ~γ (t ∷ σ) (α ∷ γ) = LR t α × LR-σ~γ σ γ

fundamental-lemma : (e : Γ ⊢ τ) (σ : Subst Γ ∅) (γ : ⟦ Γ ⟧c)
                  → LR-σ~γ σ γ
                  → LR (σ ⟪ e ⟫ˢ) (⟦ e ⟧ γ)
fundamental-lemma e σ γ σ~γ = ?

subst-∅ : (e : ∅ ⊢ τ) → ∅ ⟪ e ⟫ˢ ≡ e
subst-∅ (f ∙ t) = cong₂ _∙_ (subst-∅ f) (subst-∅ t)
subst-∅ (abs e) = cong abs {! !}
subst-∅ (# n) = refl
subst-∅ (pred e) = cong pred (subst-∅ e)
subst-∅ (succ e) = cong succ (subst-∅ e)
subst-∅ (ifz e then t₀ else t₁) = cong₃ ifz_then_else_ (subst-∅ e) (subst-∅ t₀) (subst-∅ t₁)
subst-∅ (Y f) = cong Y (subst-∅ f)


adequacy' : (e : ∅ ⊢ nat) {n : Nat} (k : Nat)
          → LR e (δ'[ k ] (now n))
          → e ⇒[ k ] # n
adequacy' e zero e~v = LR-unfoldη e~v
adequacy' e {n} (suc zero) e~δv =
  let ⟨ pair e₀ e₁ , pair e⇒e₀ (pair e₀→e₁ next[e₁]▹~v) ⟩ₛ = unfold1
  in mred-s e⇒e₀ e₀→e₁ (adequacy' e₁ zero (LR-foldη {! !}))
  where
    v : ⟦ nat ⟧t
    v = now n

    unfold1 : ∃₂ (λ e₀ e₁ → (e ⇒[ zero ] e₀) × (e₀ →[ true ] e₁) × ▹LR (next e₁) (next v))
    unfold1 = LR-unfoldθ e~δv
adequacy' e {n} (suc k) e~δ[1+k]v =
  let ⟨ pair e₀ e₁ , pair e⇒e₀ (pair e₀→e₁ next[e₁]▹~δ[k]v) ⟩ₛ = unfold1
  in mred-s e⇒e₀ e₀→e₁ (adequacy' e₁ k {! LR-foldθ !})
  where
    v : ⟦ nat ⟧t
    v = now n

    unfold1 : ∃₂ (λ e₀ e₁ → (e ⇒[ zero ] e₀) × (e₀ →[ true ] e₁) × ▹LR (next e₁) (next (δ'[ k ] v)))
    unfold1 = LR-unfoldθ e~δ[1+k]v

adequacy : (e : ∅ ⊢ nat) {n : Nat} (k : Nat)
         → ⟦ e ⟧ ∅ ≡ δ'[ k ] (now n)
         → e ⇒[ k ] # n
adequacy e {n} k ⟦e⟧=δ[k]v = adequacy' e k e~δ[k]v
  where
    v : ⟦ nat ⟧t
    v = now n

    ⟪e⟫~⟦e⟧ : LR (∅ ⟪ e ⟫ˢ) (⟦ e ⟧ ∅)
    ⟪e⟫~⟦e⟧ = fundamental-lemma e ∅ ∅ tt

    e~δ[k]v : LR e (δ'[ k ] v)
    e~δ[k]v = subst2 LR (subst-∅ e) ⟦e⟧=δ[k]v ⟪e⟫~⟦e⟧
