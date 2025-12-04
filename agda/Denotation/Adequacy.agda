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
open import Substitution.Properties
open import OpSem.SmallStep
open import Denotation.LaterAlgebra
open import Denotation.Interpretation
open import Denotation.RenSub
open import Denotation.Soundness


module Denotation.Adequacy where

▹U : ▹ Set → Set
▹U ▹A = ∀ (@tick x : Tick) → ▹A x

LR-body : ▹ (Γ ⊢ nat → ⟦ nat ⟧t → Set) → Γ ⊢ nat → ⟦ nat ⟧t → Set
LR-body ▹LR e (now n) = e ⇒[ zero ] # n
LR-body ▹LR e (future r) = ∃₂ (λ e₀ e₁ → (e ⇒[ zero ] e₀)
                                       × (e₀ →[ true ] e₁)
                                       × ▹U (▹LR ⊛ next e₁ ⊛ r))

LR : Γ ⊢ τ → ⟦ τ ⟧t → Set
LR {τ = nat} = gfix LR-body
LR {τ = τ ⇒ σ} f φ = ∀ {t α} → LR t α → LR (f ∙ t) (φ α)

▹LR : ▹ (Γ ⊢ τ) → ▹ ⟦ τ ⟧t → Set
▹LR e α = ▹U (next LR ⊛ e ⊛ α)


LR-unfoldη : {e : Γ ⊢ nat} {n : Nat} → LR e (now n) → e ⇒[ zero ] # n
LR-unfoldη {e = e} {n = n} = transport (gfix-unfold LR-body ≡$ e ≡$ (now n))

LR-unfoldθ : {e : Γ ⊢ nat} {α : ▹ ⟦ nat ⟧t} → LR e (θ' α)
           → ∃₂ (λ e₀ e₁ → (e ⇒[ zero ] e₀) × (e₀ →[ true ] e₁) × ▹LR (next e₁) α)
LR-unfoldθ {e = e} {α = α} = transport (gfix-unfold LR-body ≡$ e ≡$ (θ' α))

LR-foldη : {e : Γ ⊢ nat} {n : Nat} → e ⇒[ zero ] # n → LR e (now n)
LR-foldη {e = e} {n = n} = transport (sym (gfix-unfold LR-body ≡$ e ≡$ (now n)))

LR-foldθ : {e : Γ ⊢ nat} {α : ▹ ⟦ nat ⟧t}
         → ∃₂ (λ e₀ e₁ → (e ⇒[ zero ] e₀) × (e₀ →[ true ] e₁) × ▹LR (next e₁) α)
         → LR e (θ' α)
LR-foldθ {e = e} {α = α} = transport (sym (gfix-unfold LR-body ≡$ e ≡$ (θ' α)))


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
   in LR-foldη {!   !}
LR→[z]LR {τ = nat} e e' e→e' (future r) e~r =
  let q = LR-unfoldθ e~r 
   in LR-foldθ {!   !}
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
fundamental-lemma (var Z) (t ∷ σ) (α ∷ γ) (pair t~α σ~γ) = t~α
fundamental-lemma (var (S x)) (t ∷ σ) (α ∷ γ) (pair t~α σ~γ) = fundamental-lemma (var x) σ γ σ~γ
fundamental-lemma (f ∙ t) σ γ σ~γ = (fundamental-lemma f σ γ σ~γ)(fundamental-lemma t σ γ σ~γ)
fundamental-lemma (abs e) σ γ σ~γ {t} {α} t~α = {! IH  !}
  where
    IH = fundamental-lemma e (t ∷ σ) (α ∷ γ) (pair t~α σ~γ)
fundamental-lemma (# n) σ γ σ~γ = LR-foldη mred-refl
fundamental-lemma (pred e) σ γ σ~γ = {!  !}
  where
    IH = fundamental-lemma e σ γ σ~γ
fundamental-lemma (succ e) σ γ σ~γ = {!  !}
  where
    IH = fundamental-lemma e σ γ σ~γ
fundamental-lemma {τ = τ} (ifz e then t₀ else t₁) σ γ σ~γ = proof
  where
    IHe = fundamental-lemma e σ γ σ~γ

    M = suc-renaming (idᴿ _) ⟪ t₀ ⟫
    N = suc-renaming (idᴿ _) ⟪ t₁ ⟫
    M-eq = suc-rename-idᴿ⟦ t₀ ⟧ γ (⟦ e ⟧ γ)
    N-eq = suc-rename-idᴿ⟦ t₁ ⟧ γ (⟦ e ⟧ γ)

    red-⟪⟫ˢ : σ ⟪ (abs (ifz var Z then M else N)) ∙ e ⟫ˢ →[ false ] σ ⟪ ifz e then t₀ else t₁ ⟫ˢ
    red-⟪⟫ˢ = {!   !} -- TODO: reduction under renaming/substitution    

    [ifz]-eq : map-ext ▹alg' (nat-ifz (⟦ M ⟧ (⟦ e ⟧ γ ∷ γ)) (⟦ N ⟧ (⟦ e ⟧ γ ∷ γ))) (⟦ e ⟧ γ)
             ≡ map-ext ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ)) (⟦ e ⟧ γ)
    [ifz]-eq = cong₂ (λ [0] [1] → map-ext ▹alg' (nat-ifz [0] [1])) M-eq N-eq ≡$ (⟦ e ⟧ γ)

    abs-ifz : LR (σ ⟪ abs (ifz var Z then M else N) ⟫ˢ )
                 (⟦ abs (ifz var Z then M else N) ⟧ γ)
    abs-ifz = {!   !}

    t0 : LR (σ ⟪ abs (ifz var Z then M else N) ⟫ˢ ∙ σ ⟪ e ⟫ˢ)
            (⟦ abs (ifz var Z then M else N) ⟧ γ (⟦ e ⟧ γ))
    t0 = abs-ifz IHe

    t1 : LR (σ ⟪ ifz e then t₀ else t₁ ⟫ˢ)
            (⟦ abs (ifz var Z then M else N) ⟧ γ (⟦ e ⟧ γ))
    t1 = LR→[z]LR _ _  red-⟪⟫ˢ _ t0

    proof : LR (σ ⟪ ifz e then t₀ else t₁ ⟫ˢ) (⟦ ifz e then t₀ else t₁ ⟧ γ)
    proof = subst (LR (σ ⟪ ifz e then t₀ else t₁ ⟫ˢ)) [ifz]-eq t1

fundamental-lemma (Y f) σ γ σ~γ = proof
  where
    IHf = fundamental-lemma f σ γ σ~γ
    
    red-⟪⟫ˢ : σ ⟪ Y f ⟫ˢ →[ true ] σ ⟪ f ∙ (Y f) ⟫ˢ
    red-⟪⟫ˢ = {!   !} -- TODO: reduction under renaming/substitution

    proof : LR (σ ⟪ Y f ⟫ˢ) (⟦ Y f ⟧ γ)
    proof = gfix λ { ▹IHYf →
        let t0 : ▹ (LR (σ ⟪ f ∙ (Y f) ⟫ˢ) (⟦ f ⟧ γ (⟦ Y f ⟧ γ)))
            t0 = (next IHf) ⊛  ▹IHYf
            t1 : ▹LR (next (σ ⟪ f ∙ (Y f) ⟫ˢ)) (next (⟦ f ⟧ γ (⟦ Y f ⟧ γ)))
            t1 = t0
            t2 : LR (σ ⟪ Y f ⟫ˢ) (δ' (⟦ f ⟧ γ (⟦ Y f ⟧ γ)))
            t2 = LR→[s]θ _ _ red-⟪⟫ˢ _ t1
            t3 : LR (σ ⟪ Y f ⟫ˢ) ((⟦ Y f ⟧ γ))
            t3 = subst (LR (σ ⟪ Y f ⟫ˢ)) (sym (Y-delay f)) t2
        in  t3 }


adequacy' : (e : ∅ ⊢ nat) {n : Nat} (k : Nat)
          → LR e (δ'[ k ] (now n))
          → e ⇒[ k ] # n
adequacy' e zero e~v = LR-unfoldη e~v
adequacy' e {n} (suc k) e~δ[1+k]v =
  let ⟨ pair e₀ e₁ , pair e⇒e₀ (pair e₀→e₁ next[e₁]▹~δ[k]v) ⟩ₛ = unfold1
      IH = next (adequacy' e₁ k) ⊛ next[e₁]▹~δ[k]v
  in mred-s e⇒e₀ e₀→e₁ IH
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
    e~δ[k]v = subst2 LR (subst-id e) ⟦e⟧=δ[k]v ⟪e⟫~⟦e⟧
