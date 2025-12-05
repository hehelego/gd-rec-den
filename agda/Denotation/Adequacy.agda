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

    eq : exts σ ⟪ e ⟫ˢ [ t ] ≡ (t ∷ σ) ⟪ e ⟫ˢ
    eq =
      exts σ ⟪ e ⟫ˢ [ t ]
        ≡⟨⟩
      (t ∷ idˢ _) ⟪ exts σ ⟪ e ⟫ˢ ⟫ˢ
        ≡⟨ sym (subst-◆ (t ∷ idˢ _) (exts σ) e) ⟩
      (t ∷ idˢ _) ◆ exts σ ⟪ e ⟫ˢ
        ≡⟨ subst-ext-var ((t ∷ idˢ _) ◆ exts σ) (t ∷ σ) 
                         subst-var-eq
                         e ⟩
      (t ∷ σ) ⟪ e ⟫ˢ ∎

    red' : σ ⟪ abs e ⟫ˢ ∙ t →[ false ] (t ∷ σ) ⟪ e ⟫ˢ
    red' = subst (σ ⟪ abs e ⟫ˢ ∙ t →[ false ]_) eq red

    proof : LR (σ ⟪ abs e ⟫ˢ ∙ t) (⟦ e ⟧ (α ∷ γ))
    proof = LR←[z]LR red' IH
fundamental-lemma (# n) σ γ σ~γ = LR-foldη mred-refl
fundamental-lemma (pred e) σ γ σ~γ = {!!}
  where
    IH = fundamental-lemma e σ γ σ~γ
    e⇒v = transport (gfix-unfold LR-body ≡$ σ ⟪ e ⟫ˢ ≡$ ⟦ e ⟧ γ) IH
fundamental-lemma (succ e) σ γ σ~γ = {!!}
  where
    IH = fundamental-lemma e σ γ σ~γ
    e⇒v = transport (gfix-unfold LR-body ≡$ σ ⟪ e ⟫ˢ ≡$ ⟦ e ⟧ γ) IH
fundamental-lemma {Γ = Γ} (ifz e then t₀ else t₁) σ γ σ~γ = proof
  where
    IHe = fundamental-lemma e σ γ σ~γ
    IHt₀ = fundamental-lemma t₀ σ γ σ~γ
    IHt₁ = fundamental-lemma t₁ σ γ σ~γ

    M = suc-renaming (idᴿ _) ⟪ t₀ ⟫
    N = suc-renaming (idᴿ _) ⟪ t₁ ⟫
    M-eq = λ {e : Γ ⊢ nat} → suc-rename-idᴿ⟦ t₀ ⟧ γ (⟦ e ⟧ γ)
    N-eq = λ {e : Γ ⊢ nat} → suc-rename-idᴿ⟦ t₁ ⟧ γ (⟦ e ⟧ γ)
    M-eq' = λ {e : Γ ⊢ nat} → cong (σ ⟪_⟫ˢ) (subst0-cancel-shift t₀ e)
    N-eq' = λ {e : Γ ⊢ nat} → cong (σ ⟪_⟫ˢ) (subst0-cancel-shift t₁ e)

    red-⟪ifz⟫ˢ : σ ⟪ abs (ifz var Z then M else N) ∙ e ⟫ˢ
      →[ false ] σ ⟪ ifz e then M [ e ] else N [ e ] ⟫ˢ
    red-⟪ifz⟫ˢ = σ ⟪→ red-beta {f = ifz var Z then M else N} {t = e} ⟫ˢ

    red-⟪⟫ˢ : σ ⟪ (abs (ifz var Z then M else N)) ∙ e ⟫ˢ
      →[ false ] σ ⟪ ifz e then t₀ else t₁ ⟫ˢ
    red-⟪⟫ˢ = subst2 (λ m* n* → σ ⟪ (abs (ifz var Z then M else N)) ∙ e ⟫ˢ
                      →[ false ] ifz σ ⟪ e ⟫ˢ then m* else n*)
              M-eq' N-eq'
              red-⟪ifz⟫ˢ
    

    [ifz]-eq : map-ext ▹alg' (nat-ifz (⟦ M ⟧ (⟦ e ⟧ γ ∷ γ)) (⟦ N ⟧ (⟦ e ⟧ γ ∷ γ))) (⟦ e ⟧ γ)
             ≡ map-ext ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ)) (⟦ e ⟧ γ)
    [ifz]-eq = cong₂ (λ [0] [1] → map-ext ▹alg' (nat-ifz [0] [1]) (⟦ e ⟧ γ)) (M-eq {e}) (N-eq {e})

    abs-ifz-body : ▹ (LR (σ ⟪ abs (ifz var Z then M else N) ⟫ˢ )
                         (⟦ abs (ifz var Z then M else N) ⟧ γ))
                 →    LR (σ ⟪ abs (ifz var Z then M else N) ⟫ˢ )
                         (⟦ abs (ifz var Z then M else N) ⟧ γ)
    abs-ifz-body ▹IH {s} v@{now zero} s~α =
      let M[s]=t₀ : exts σ ⟪ M ⟫ˢ [ s ] ≡ σ ⟪ t₀ ⟫ˢ
          M[s]=t₀ =
            exts σ ⟪ M ⟫ˢ [ s ]
              ≡⟨⟩
            exts σ ⟪ suc-renaming (idᴿ _) ⟪ t₀ ⟫ ⟫ˢ [ s ]
              ≡⟨ cong (_[ s ]) (sym (ren⟪σ⟪t⟫ˢ⟫≡σ⟪ren⟪t⟫⟫ˢ σ t₀)) ⟩
            suc-renaming (idᴿ ∅) ⟪ σ ⟪ t₀ ⟫ˢ ⟫ [ s ]
              ≡⟨ subst0-cancel-shift (σ ⟪ t₀ ⟫ˢ) s ⟩
            σ ⟪ t₀ ⟫ˢ ∎

          s⇒v = LR-unfoldη s~α
          ifs⇒ifv⇒M = mred-trans (mred-z red-beta (mred-ifz s⇒v)) (mred-red red-ifz-z)
          ifs⇒ifv⇒t₀ = subst (abs (ifz var Z then exts σ ⟪ M ⟫ˢ else exts σ ⟪ N ⟫ˢ) ∙ s ⇒[ zero ]_) M[s]=t₀ ifs⇒ifv⇒M
          LR-gfix = LR⇐[z]LR ifs⇒ifv⇒t₀ IHt₀

          sem-eq : map-ext ▹alg' (nat-ifz (⟦ M ⟧ (v ∷ γ)) (⟦ N ⟧ (v ∷ γ))) v ≡ ⟦ t₀ ⟧ γ
          sem-eq =
            map-ext ▹alg' (nat-ifz (⟦ M ⟧ (v ∷ γ)) (⟦ N ⟧ (v ∷ γ))) v
              ≡⟨ gfix-unfold _ ≡$ v ⟩
            ⟦ M ⟧ (v ∷ γ)
              ≡⟨ M-eq {e = # zero} ⟩
            ⟦ t₀ ⟧ γ ∎

       in subst (LR (abs (ifz var Z then exts σ ⟪ M ⟫ˢ else exts σ ⟪ N ⟫ˢ) ∙ s)) (sym sem-eq) LR-gfix
    abs-ifz-body ▹IH {s} v@{now (suc n)} s~α =
      let N[s]=t₁ : exts σ ⟪ N ⟫ˢ [ s ] ≡ σ ⟪ t₁ ⟫ˢ
          N[s]=t₁ =
            exts σ ⟪ N ⟫ˢ [ s ]
              ≡⟨⟩
            exts σ ⟪ suc-renaming (idᴿ _) ⟪ t₁ ⟫ ⟫ˢ [ s ]
              ≡⟨ cong (_[ s ]) (sym (ren⟪σ⟪t⟫ˢ⟫≡σ⟪ren⟪t⟫⟫ˢ σ t₁)) ⟩
            suc-renaming (idᴿ ∅) ⟪ σ ⟪ t₁ ⟫ˢ ⟫ [ s ]
              ≡⟨ subst0-cancel-shift (σ ⟪ t₁ ⟫ˢ) s ⟩
            σ ⟪ t₁ ⟫ˢ ∎

          s⇒v = LR-unfoldη s~α
          ifs⇒ifv⇒N = mred-trans (mred-z red-beta (mred-ifz s⇒v)) (mred-red red-ifz-s)
          ifs⇒ifv⇒t₁ = subst (abs (ifz var Z then exts σ ⟪ M ⟫ˢ else exts σ ⟪ N ⟫ˢ) ∙ s ⇒[ zero ]_) N[s]=t₁ ifs⇒ifv⇒N
          LR-gfix = LR⇐[z]LR ifs⇒ifv⇒t₁ IHt₁

          sem-eq : map-ext ▹alg' (nat-ifz (⟦ M ⟧ (v ∷ γ)) (⟦ N ⟧ (now (suc n) ∷ γ))) (now (suc n)) ≡ ⟦ t₁ ⟧ γ
          sem-eq =
            map-ext ▹alg' (nat-ifz (⟦ M ⟧ (v ∷ γ)) (⟦ N ⟧ (v ∷ γ))) v
              ≡⟨ gfix-unfold _ ≡$ v ⟩
            ⟦ N ⟧ (now (suc n) ∷ γ)
              ≡⟨ N-eq {e = # (suc n)} ⟩
            ⟦ t₁ ⟧ γ ∎

       in subst (LR (abs (ifz var Z then exts σ ⟪ M ⟫ˢ else exts σ ⟪ N ⟫ˢ) ∙ s)) (sym sem-eq) LR-gfix
    abs-ifz-body ▹IH {s} {future r} s~α = {!   !}

    LR-abs-ifz : LR (σ ⟪ abs (ifz var Z then M else N) ⟫ˢ )
                    (⟦ abs (ifz var Z then M else N) ⟧ γ)
    LR-abs-ifz = gfix abs-ifz-body

    LR-abs-ifz-app : LR (σ ⟪ abs (ifz var Z then M else N) ⟫ˢ ∙ σ ⟪ e ⟫ˢ)
                        (⟦ abs (ifz var Z then M else N) ⟧ γ (⟦ e ⟧ γ))
    LR-abs-ifz-app = LR-abs-ifz IHe

    LR-ifz-weaken : LR (σ ⟪ ifz e then t₀ else t₁ ⟫ˢ)
                       (⟦ abs (ifz var Z then M else N) ⟧ γ (⟦ e ⟧ γ))
    LR-ifz-weaken = LR→[z]LR red-⟪⟫ˢ LR-abs-ifz-app

    proof : LR (σ ⟪ ifz e then t₀ else t₁ ⟫ˢ) (⟦ ifz e then t₀ else t₁ ⟧ γ)
    proof = subst (LR (σ ⟪ ifz e then t₀ else t₁ ⟫ˢ)) [ifz]-eq LR-ifz-weaken

fundamental-lemma (Y f) σ γ σ~γ = proof
  where
    IHf = fundamental-lemma f σ γ σ~γ
    
    red-⟪⟫ˢ : σ ⟪ Y f ⟫ˢ →[ true ] σ ⟪ f ∙ (Y f) ⟫ˢ
    red-⟪⟫ˢ = σ ⟪→ red-unfold {f = f} ⟫ˢ

    proof : LR (σ ⟪ Y f ⟫ˢ) (⟦ Y f ⟧ γ)
    proof = gfix λ { ▹IHYf →
        let t0 : ▹ (LR (σ ⟪ f ∙ (Y f) ⟫ˢ) (⟦ f ⟧ γ (⟦ Y f ⟧ γ)))
            t0 = (next IHf) ⊛  ▹IHYf
            t1 : ▹LR (next (σ ⟪ f ∙ (Y f) ⟫ˢ)) (next (⟦ f ⟧ γ (⟦ Y f ⟧ γ)))
            t1 = t0
            t2 : LR (σ ⟪ Y f ⟫ˢ) (δ' (⟦ f ⟧ γ (⟦ Y f ⟧ γ)))
            t2 = LR→[s]θ red-⟪⟫ˢ t1
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
