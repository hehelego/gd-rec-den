open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Cubical.Foundations.Prelude hiding (Type; _,_; _∙_; cong; cong₂; cong₃)

open import Helper
open import Term
open import LaterPrims

open import OpSem.SmallStep
open import Renaming
open import Substitution

module OpSem.SProperties where


→-deterministic : {e e₁ e₂ : Γ ⊢ τ} {k : Bool}
                → e →[ k ] e₁
                → e →[ k ] e₂
                → e₁ ≡ e₂
→-deterministic (red-app {t = t} f→f') (red-app f→f'') = cong (_∙ t) (→-deterministic f→f' f→f'')
→-deterministic red-beta red-beta = refl
→-deterministic (red-ifz {t₀ = t₀} {t₁ = t₁} e→e') (red-ifz e→e'') = cong (ifz_then t₀ else t₁) (→-deterministic e→e' e→e'')
→-deterministic (red-pred e→e') (red-pred e→e'') = cong pred (→-deterministic e→e' e→e'')
→-deterministic (red-succ e→e') (red-succ e→e'') = cong succ (→-deterministic e→e' e→e'')
→-deterministic red-pred' red-pred' = refl
→-deterministic red-succ' red-succ' = refl
→-deterministic red-ifz-z red-ifz-z = refl
→-deterministic red-ifz-s red-ifz-s = refl
→-deterministic red-unfold red-unfold = refl

absurd→[z][s] : {e e₀ e₁ : Γ ⊢ τ} 
               → e →[ false ] e₀
               → e →[ true  ] e₁
               → ⊥
absurd→[z][s] (red-app f₀) (red-app f₁) = absurd→[z][s] f₀ f₁
absurd→[z][s] (red-ifz e₀) (red-ifz e₁) = absurd→[z][s] e₀ e₁
absurd→[z][s] (red-pred e₀) (red-pred e₁) = absurd→[z][s] e₀ e₁
absurd→[z][s] (red-succ e₀) (red-succ e₁) = absurd→[z][s] e₀ e₁


infix 5 _⟪→_⟫
infix 5 _⟪→_⟫ˢ
infix 5 _⟪⇒_⟫
infix 5 _⟪⇒_⟫ˢ

-- rename-▷ ρ {abs t ∙ s} {r} β = subst (ρ ⟪ abs t ∙ s ⟫ ▷_) (sym (rename-[] t s ρ)) β

_⟪→_⟫ : (ρ : Renaming Γ Δ)
      → {e e' : Γ ⊢ τ} {k : Bool}
      → e →[ k ] e'
      → ρ ⟪ e ⟫ →[ k ] ρ ⟪ e' ⟫
ρ ⟪→ red-app f→f' ⟫ = red-app (ρ ⟪→ f→f' ⟫)
ρ ⟪→ red-beta {f = f} {t = t} ⟫ = red'
  where
    eq : ext ρ ⟪ f ⟫ [ ρ ⟪ t ⟫ ] ≡ ρ ⟪ f [ t ] ⟫
    eq = sym (rename-[] f t ρ)

    red : ρ ⟪ abs f ∙ t ⟫ →[ false ] ext ρ ⟪ f ⟫ [ ρ ⟪ t ⟫ ]
    red = red-beta

    red' : ρ ⟪ abs f ∙ t ⟫ →[ false ] ρ ⟪ f [ t ] ⟫
    red' = subst (ρ ⟪ abs f ∙ t ⟫ →[ false ]_) eq red
ρ ⟪→ red-ifz e→e' ⟫ = red-ifz (ρ ⟪→ e→e' ⟫)
ρ ⟪→ red-pred e→e' ⟫ = red-pred (ρ ⟪→ e→e' ⟫)
ρ ⟪→ red-succ e→e' ⟫ = red-succ (ρ ⟪→ e→e' ⟫)
ρ ⟪→ red-pred' ⟫ = red-pred'
ρ ⟪→ red-succ' ⟫ = red-succ'
ρ ⟪→ red-ifz-z ⟫ = red-ifz-z
ρ ⟪→ red-ifz-s ⟫ = red-ifz-s
ρ ⟪→ red-unfold ⟫ = red-unfold

_⟪→_⟫ˢ : (σ : Subst Γ Δ)
       → {e e' : Γ ⊢ τ} {k : Bool}
       → e →[ k ] e'
       → σ ⟪ e ⟫ˢ →[ k ] σ ⟪ e' ⟫ˢ
σ ⟪→ red-app f→f' ⟫ˢ = red-app (σ ⟪→ f→f' ⟫ˢ)
σ ⟪→ red-beta {f = f} {t = t} ⟫ˢ = red'
  where
    eq : exts σ ⟪ f ⟫ˢ [ σ ⟪ t ⟫ˢ ] ≡ σ ⟪ f [ t ] ⟫ˢ
    eq = sym (subst-[] f t σ)

    red : σ ⟪ abs f ∙ t ⟫ˢ →[ false ] exts σ ⟪ f ⟫ˢ [ σ ⟪ t ⟫ˢ ]
    red = red-beta

    red' : σ ⟪ abs f ∙ t ⟫ˢ →[ false ] σ ⟪ f [ t ] ⟫ˢ
    red' = subst (σ ⟪ abs f ∙ t ⟫ˢ →[ false ]_) eq red
σ ⟪→ red-ifz e→e' ⟫ˢ = red-ifz (σ ⟪→ e→e' ⟫ˢ)
σ ⟪→ red-pred e→e' ⟫ˢ = red-pred (σ ⟪→ e→e' ⟫ˢ)
σ ⟪→ red-succ e→e' ⟫ˢ = red-succ (σ ⟪→ e→e' ⟫ˢ)
σ ⟪→ red-pred' ⟫ˢ = red-pred'
σ ⟪→ red-succ' ⟫ˢ = red-succ'
σ ⟪→ red-ifz-z ⟫ˢ = red-ifz-z
σ ⟪→ red-ifz-s ⟫ˢ = red-ifz-s
σ ⟪→ red-unfold ⟫ˢ = red-unfold


_⟪⇒_⟫ : (ρ : Renaming Γ Δ)
      → {e e' : Γ ⊢ τ} {k : Nat}
      → e ⇒[ k ] e'
      → ρ ⟪ e ⟫ ⇒[ k ] ρ ⟪ e' ⟫
ρ ⟪⇒ mred-refl ⟫ = mred-refl
ρ ⟪⇒ mred-z e→e'' e''⇒e' ⟫ = mred-z (ρ ⟪→ e→e'' ⟫) (ρ ⟪⇒ e''⇒e' ⟫)
ρ ⟪⇒ mred-s e⇒e₀ e₀→e₁ ▹e₁⇒e' ⟫ = mred-s (ρ ⟪⇒ e⇒e₀ ⟫) (ρ ⟪→ e₀→e₁ ⟫) (next (ρ ⟪⇒_⟫) ⊛ ▹e₁⇒e')

_⟪⇒_⟫ˢ : (σ : Subst Γ Δ)
       → {e e' : Γ ⊢ τ} {k : Nat}
       → e ⇒[ k ] e'
       → σ ⟪ e ⟫ˢ ⇒[ k ] σ ⟪ e' ⟫ˢ
σ ⟪⇒ mred-refl ⟫ˢ = mred-refl
σ ⟪⇒ mred-z e→e'' e''⇒e' ⟫ˢ = mred-z (σ ⟪→ e→e'' ⟫ˢ) (σ ⟪⇒ e''⇒e' ⟫ˢ)
σ ⟪⇒ mred-s e⇒e₀ e₀→e₁ ▹e₁⇒e' ⟫ˢ = mred-s (σ ⟪⇒ e⇒e₀ ⟫ˢ) (σ ⟪→ e₀→e₁ ⟫ˢ) (next (σ ⟪⇒_⟫ˢ) ⊛ ▹e₁⇒e')