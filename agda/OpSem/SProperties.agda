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