open import Cubical.Foundations.Prelude hiding (Type; _,_; _∙_; cong; cong₂; cong₃; lift)

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
open import OpSem.SProperties
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


LR→[s]θ : {e e' : Γ ⊢ τ} → e →[ true ] e'
        → {α : ▹ ⟦ τ ⟧t}
        → ▹LR (next e') α
        → LR e (θ' α)
LR→[s]θ {τ = nat} {e = e} {e' = e'} e→e' ▹R
  = LR-foldθ ⟨ pair e e' , pair mred-refl (pair e→e' ▹R) ⟩ₛ
LR→[s]θ {τ = τ ⇒ σ} f→f' {φ} next[f]▹~φ {t} {α} t~α
  = LR→[s]θ {τ = σ} (red-app f→f') {φ ⊛ next α} (LR⊛ next[f]▹~φ (next t~α))

LR→[z]LR : {e e' : Γ ⊢ τ} → e →[ false ] e'
         → {α : ⟦ τ ⟧t}
         → LR e  α
         → LR e' α
LR→[z]LR {τ = nat} e→e' {now n} e~α 
  with LR-unfoldη e~α
... | mred-z e→e'' e''⇒n = let e''=e' = →-deterministic e→e'' e→e'
                               e'⇒n = subst (_⇒[ zero ] # n) e''=e' e''⇒n
                            in LR-foldη e'⇒n
LR→[z]LR {τ = nat} e→e' {future r} e~α
  with LR-unfoldθ e~α
... | ⟨ pair e₀ e₁ , pair e⇒e₀ (pair e₀→e₁ next[e₁]▹~r) ⟩ₛ
  with e⇒e₀
... | mred-refl = absurd (absurd→[z][s] e→e' e₀→e₁)
... | mred-z e→e'' e''⇒e₀ = let e''=e' = →-deterministic e→e'' e→e'
                                e'⇒e₀ = subst (_⇒[ zero ] e₀) e''=e' e''⇒e₀
                             in LR-foldθ ⟨ pair e₀ e₁ , pair e'⇒e₀ (pair e₀→e₁ next[e₁]▹~r) ⟩ₛ
LR→[z]LR {τ = τ ⇒ σ} f→f' {φ} f~φ {t} {α} t~α
  = LR→[z]LR {τ = σ} (red-app f→f') {φ α} (f~φ t~α)


▹LR→[z]LR : {e e' : Γ ⊢ τ} → e →[ false ] e'
          → {α : ▹ ⟦ τ ⟧t}
          → ▹LR (next e ) α
          → ▹LR (next e') α
▹LR→[z]LR e→e' e~α κ = LR→[z]LR e→e' (e~α κ)

LR←[z]LR : {e e' : Γ ⊢ τ} → e →[ false ] e'
         → {α : ⟦ τ ⟧t}
         → LR e' α
         → LR e  α
LR←[z]LR {τ = nat} e→e' {now n} e'~α =
  let e'⇒n = LR-unfoldη e'~α
   in LR-foldη (mred-z e→e' e'⇒n)
LR←[z]LR {τ = nat} e→e' {future r} e'~α =
  let ⟨ pair e₀ e₁ , pair e'⇒e₀ (pair e₀→e₁ next[e₁]▹~r) ⟩ₛ = LR-unfoldθ e'~α
   in LR-foldθ ⟨ pair e₀ e₁ , pair (mred-z e→e' e'⇒e₀) (pair e₀→e₁ next[e₁]▹~r) ⟩ₛ
LR←[z]LR {τ = τ ⇒ σ} f→f' {φ} f'~φ {t} {α} t~α
  = LR←[z]LR {τ = σ} (red-app f→f') {φ α} (f'~φ t~α)


LR⇐[z]LR : {e e' : Γ ⊢ τ} → e ⇒[ zero ] e'
         → {α : ⟦ τ ⟧t}
         → LR e' α
         → LR e  α
LR⇐[z]LR mred-refl e'~α = e'~α
LR⇐[z]LR (mred-z e→e'' e''⇒e') e'~α = let e''~α = LR⇐[z]LR e''⇒e' e'~α
                                       in LR←[z]LR e→e'' e''~α


LR-σ~γ : Subst Γ ∅ → ⟦ Γ ⟧c → Set
LR-σ~γ ∅ ∅ = ⊤
LR-σ~γ (t ∷ σ) (α ∷ γ) = LR t α × LR-σ~γ σ γ

fundamental-lemma : (e : Γ ⊢ τ) (σ : Subst Γ ∅) (γ : ⟦ Γ ⟧c)
                  → LR-σ~γ σ γ
                  → LR (σ ⟪ e ⟫ˢ) (⟦ e ⟧ γ)
fundamental-lemma (var Z) (t ∷ σ) (α ∷ γ) (pair t~α σ~γ) = t~α
fundamental-lemma (var (S x)) (t ∷ σ) (α ∷ γ) (pair t~α σ~γ) = fundamental-lemma (var x) σ γ σ~γ
fundamental-lemma (f ∙ t) σ γ σ~γ = (fundamental-lemma f σ γ σ~γ)(fundamental-lemma t σ γ σ~γ)
fundamental-lemma {Γ = Γ} {τ = τ₁ ⇒ τ₂} (abs e) σ γ σ~γ {t} {α} t~α = proof
  where
    IH : LR ((t ∷ σ) ⟪ e ⟫ˢ) (⟦ e ⟧ (α ∷ γ))
    IH = fundamental-lemma e (t ∷ σ) (α ∷ γ) (pair t~α σ~γ)

    red : σ ⟪ abs e ⟫ˢ ∙ t →[ false ] exts σ ⟪ e ⟫ˢ [ t ]
    red = red-beta

    subst-var-eq : (τ : Type) (x : Γ , τ₁ ∋ τ) →
      (t ∷ ((t ∷ ∅) ◆ suc-subst σ)) ⟨ x ⟩ˢ ≡ (t ∷ σ) ⟨ x ⟩ˢ
    subst-var-eq τ Z = refl
    subst-var-eq τ (S x) = sym (subst-outer-abs-suc-subst σ t  x)

    subst-eq : exts σ ⟪ e ⟫ˢ [ t ] ≡ (t ∷ σ) ⟪ e ⟫ˢ
    subst-eq =
      exts σ ⟪ e ⟫ˢ [ t ]
        ≡⟨⟩
      (t ∷ idˢ _) ⟪ exts σ ⟪ e ⟫ˢ ⟫ˢ
        ≡⟨ sym (subst-◆ (t ∷ idˢ _) (exts σ) e) ⟩
      (t ∷ idˢ _) ◆ exts σ ⟪ e ⟫ˢ
        ≡⟨ subst-ext-var ((t ∷ idˢ _) ◆ exts σ) (t ∷ σ) 
                         subst-var-eq
                         e ⟩
      (t ∷ σ) ⟪ e ⟫ˢ ∎

    red-beta-⟪⟫ˢ : σ ⟪ abs e ⟫ˢ ∙ t →[ false ] (t ∷ σ) ⟪ e ⟫ˢ
    red-beta-⟪⟫ˢ = subst (σ ⟪ abs e ⟫ˢ ∙ t →[ false ]_)
                         subst-eq
                         red

    proof : LR (σ ⟪ abs e ⟫ˢ ∙ t) (⟦ e ⟧ (α ∷ γ))
    proof = LR←[z]LR red-beta-⟪⟫ˢ IH
fundamental-lemma (# n) σ γ σ~γ = LR-foldη mred-refl
fundamental-lemma (pred e) σ γ σ~γ = proof
  where
    pred-LR-body : ▹ ((e : ∅ ⊢ nat) (α : ⟦ nat ⟧t) (e~α : LR e α) → LR (pred e) (𝓛-map nat-pred α))
                 →    (e : ∅ ⊢ nat) (α : ⟦ nat ⟧t) (e~α : LR e α) → LR (pred e) (𝓛-map nat-pred α)
    pred-LR-body ▹IH e α@(now n) e~α
      = let e⇒n = LR-unfoldη e~α
            pred-e⇒sn = mred-trans (mred-pred e⇒n) (mred-red red-pred')
         in LR-foldη pred-e⇒sn
    pred-LR-body ▹IH e α@(future r) e~α
      = let ⟨ pair e₀ e₁ , pair e⇒e₀ (pair e₀→e₁ next[e₁]▹~r) ⟩ₛ = LR-unfoldθ e~α
            
            LR0 : ▹LR (next (pred e₁)) (𝓛-map nat-pred ▹$ r)
            LR0 κ = (▹IH κ) e₁ (r κ) (next[e₁]▹~r κ)

            LR1 : LR (pred e₀) (𝓛-map nat-pred α)
            LR1 = LR→[s]θ (red-pred e₀→e₁) LR0

            LR2 : LR (pred e) (𝓛-map nat-pred α)
            LR2 = LR⇐[z]LR (mred-pred e⇒e₀) LR1
        in LR2

    pred-LR : (e : ∅ ⊢ nat) (α : ⟦ nat ⟧t)
            → LR e α
            → LR (pred e) (𝓛-map nat-pred α)
    pred-LR = gfix pred-LR-body

    proof : LR (σ ⟪ pred e ⟫ˢ) (⟦ pred e ⟧ γ)
    proof = pred-LR (σ ⟪ e ⟫ˢ) (⟦ e ⟧ γ) (fundamental-lemma e σ γ σ~γ)
fundamental-lemma {Γ = Γ} (succ e) σ γ σ~γ = proof
  where
    succ-LR-body : ▹ ((e : ∅ ⊢ nat) (α : ⟦ nat ⟧t) (e~α : LR e α) → LR (succ e) (𝓛-map nat-succ α))
                 →    (e : ∅ ⊢ nat) (α : ⟦ nat ⟧t) (e~α : LR e α) → LR (succ e) (𝓛-map nat-succ α)
    succ-LR-body ▹IH e α@(now n) e~α
      = let e⇒n = LR-unfoldη e~α
            succ-e⇒sn = mred-trans (mred-succ e⇒n) (mred-red red-succ')
         in LR-foldη succ-e⇒sn
    succ-LR-body ▹IH e α@(future r) e~α
      = let ⟨ pair e₀ e₁ , pair e⇒e₀ (pair e₀→e₁ next[e₁]▹~r) ⟩ₛ = LR-unfoldθ e~α
            
            LR0 : ▹LR (next (succ e₁)) (𝓛-map nat-succ ▹$ r)
            LR0 κ = (▹IH κ) e₁ (r κ) (next[e₁]▹~r κ)

            LR1 : LR (succ e₀) (𝓛-map nat-succ α)
            LR1 = LR→[s]θ (red-succ e₀→e₁) LR0

            LR2 : LR (succ e) (𝓛-map nat-succ α)
            LR2 = LR⇐[z]LR (mred-succ e⇒e₀) LR1
        in LR2

    succ-LR : (e : ∅ ⊢ nat) (α : ⟦ nat ⟧t)
            → LR e α
            → LR (succ e) (𝓛-map nat-succ α)
    succ-LR = gfix succ-LR-body

    proof : LR (σ ⟪ succ e ⟫ˢ) (⟦ succ e ⟧ γ)
    proof = succ-LR (σ ⟪ e ⟫ˢ) (⟦ e ⟧ γ) (fundamental-lemma e σ γ σ~γ)
fundamental-lemma {Γ = Γ} (ifz e then t₀ else t₁) σ γ σ~γ = proof
  where
    LR-ifz : (t₀ t₁ : ∅ ⊢ τ) (α₀ α₁ : ⟦ τ ⟧t)
           → (t₀~α₀ : LR t₀ α₀) (t₁~α₁ : LR t₁ α₁)
           → (e : ∅ ⊢ nat) (β : ⟦ nat ⟧t) (e~β : LR e β)
           → LR (ifz e then t₀ else t₁)
                (map-ext ▹alg' (nat-ifz α₀ α₁) β)
    LR-ifz t₀ t₁ α₀ α₁ t₀~α₀ t₁~α₁ = gfix λ 
        { ▹IH e (now zero) e~β →
          let e⇒v = LR-unfoldη e~β
              
              LR1 : LR (ifz # zero then t₀ else t₁) α₀
              LR1 = LR←[z]LR red-ifz-z t₀~α₀
              
              LR2 : LR (ifz e then t₀ else t₁) α₀
              LR2 = LR⇐[z]LR (mred-ifz e⇒v) LR1

              sem-eq : α₀ ≡ map-ext ▹alg' (nat-ifz α₀ α₁) (now zero)
              sem-eq = sym (gfix-unfold _ ≡$ now zero)
              in subst (LR (ifz e then t₀ else t₁)) sem-eq LR2
        ; ▹IH e (now (suc n)) e~β → 
          let e⇒v = LR-unfoldη e~β

              LR1 : LR (ifz # (suc n) then t₀ else t₁) α₁
              LR1 = LR←[z]LR red-ifz-s t₁~α₁

              LR2 : LR (ifz e then t₀ else t₁) α₁
              LR2 = LR⇐[z]LR (mred-ifz e⇒v) LR1

              sem-eq : α₁ ≡ map-ext ▹alg' (nat-ifz α₀ α₁) (now (suc n))
              sem-eq = sym (gfix-unfold _ ≡$ now (suc n))
           in subst (LR (ifz e then t₀ else t₁)) sem-eq LR2
        ; ▹IH e β@(future r) e~β →
          let ⟨ pair e₀ e₁ , pair e⇒e₀ (pair e₀→e₁ next[e₁]▹~r) ⟩ₛ = LR-unfoldθ e~β

              LR1 : ▹LR (next (ifz e₁ then t₀ else t₁))
                        (map-ext ▹alg' (nat-ifz α₀ α₁) ▹$ r)
              LR1 = λ κ → (▹IH κ) e₁ (r κ) (next[e₁]▹~r κ) 

              LR2 : LR (ifz e₀ then t₀ else t₁)
                       (θ' (map-ext ▹alg' (nat-ifz α₀ α₁) ▹$ r))
              LR2 = LR→[s]θ (red-ifz e₀→e₁) LR1

              LR3 : LR (ifz e then t₀ else t₁)
                       (θ' (map-ext ▹alg' (nat-ifz α₀ α₁) ▹$ r))
              LR3 = LR⇐[z]LR (mred-ifz e⇒e₀) LR2

              sem-eq : θ' (map-ext ▹alg' (nat-ifz α₀ α₁) ▹$ r)
                     ≡ map-ext ▹alg' (nat-ifz α₀ α₁) β
              sem-eq = sym (gfix-unfold _) ≡$ β
           in subst (LR (ifz e then t₀ else t₁)) sem-eq LR3 }

    proof : LR (σ ⟪ ifz e then t₀ else t₁ ⟫ˢ) (⟦ ifz e then t₀ else t₁ ⟧ γ)
    proof = LR-ifz (σ ⟪ t₀ ⟫ˢ) (σ ⟪ t₁ ⟫ˢ) (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ)
                   (fundamental-lemma t₀ σ γ σ~γ)
                   (fundamental-lemma t₁ σ γ σ~γ)
                   (σ ⟪ e ⟫ˢ) (⟦ e ⟧ γ) (fundamental-lemma e σ γ σ~γ)

fundamental-lemma (Y f) σ γ σ~γ = proof
  where
    IHf = fundamental-lemma f σ γ σ~γ
    
    red-⟪⟫ˢ : σ ⟪ Y f ⟫ˢ →[ true ] σ ⟪ f ∙ (Y f) ⟫ˢ
    red-⟪⟫ˢ = σ ⟪→ red-unfold {f = f} ⟫ˢ

    proof : LR (σ ⟪ Y f ⟫ˢ) (⟦ Y f ⟧ γ)
    proof = gfix λ { ▹IHYf →
        let LR1 : ▹LR (next (σ ⟪ f ∙ (Y f) ⟫ˢ))
                      (next (⟦ f ⟧ γ (⟦ Y f ⟧ γ)))
            LR1 = (next IHf) ⊛ ▹IHYf
            
            LR2 : LR (σ ⟪ Y f ⟫ˢ)
                     (δ' (⟦ f ⟧ γ (⟦ Y f ⟧ γ)))
            LR2 = LR→[s]θ red-⟪⟫ˢ LR1

            sem-eq : δ' (⟦ f ⟧ γ (⟦ Y f ⟧ γ)) ≡ ⟦ Y f ⟧ γ
            sem-eq = sym (Y-delay f)

          in subst (LR (σ ⟪ Y f ⟫ˢ)) sem-eq LR2 }


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
