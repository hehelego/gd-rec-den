open import Denotation.LaterAlgebra public
open import Denotation.Interpretation public
open import Denotation.RenSub public
open import Denotation.Soundness public
open import Denotation.Adequacy public

{-


weak0 : ∀ {Γ τ σ} → Γ ⊢ σ → Γ , τ ⊢ σ
weak0 e = suc-renaming (idᴿ _) ⟪ e ⟫

⟦weak0⟧ : ∀ {Γ σ τ} (e : Γ ⊢ σ) {γ : ⟦ Γ ⟧c} {β : ⟦ τ ⟧t}
        → ⟦ weak0 e ⟧ p⟨ γ , β ⟩ ≡ ⟦ e ⟧ γ
⟦weak0⟧ (var n) {γ} {β} =
    ⟦ weak0 (var n) ⟧ p⟨ γ , β ⟩
        ≡⟨⟩
    ⟦ var (suc-renaming (idᴿ _) ⟨ n ⟩) ⟧ p⟨ γ , β ⟩
        ≡⟨ cong (λ - → ⟦ var - ⟧ p⟨ γ , β ⟩) wk-lookup ⟩
    ⟦ var (S n) ⟧ p⟨ γ , β ⟩
        ≡⟨⟩
    ⟦ var n ⟧ γ ∎
    where
      wk-lookup : suc-renaming (idᴿ _) ⟨ n ⟩ ≡ S n
      wk-lookup =
        suc-renaming (idᴿ _) ⟨ n ⟩
            ≡⟨ suc-renaming-⟨-⟩ (idᴿ _) n ⟩
        S (idᴿ _ ⟨ n ⟩)
            ≡⟨ cong S_ (rename-idⱽ n) ⟩
        S n ∎
⟦weak0⟧ (f ∙ t) = cong₂ (λ x y → x y) (⟦weak0⟧ f) (⟦weak0⟧ t)
⟦weak0⟧ (abs e) = {! !}
⟦weak0⟧ (# n) = refl
⟦weak0⟧ (pred e) = cong (𝓛-map nat-pred) (⟦weak0⟧ e)
⟦weak0⟧ (succ e) = cong (𝓛-map nat-succ) (⟦weak0⟧ e)
⟦weak0⟧ (ifz e then t₀ else t₁) = cong₃ (λ [e] [0] [1] → map-ext ▹alg' (nat-ifz [0] [1]) [e])
                                        (⟦weak0⟧ e) (⟦weak0⟧ t₀) (⟦weak0⟧ t₁)
⟦weak0⟧ (Y f) = cong (λ [f] → gfix (λ x → θ' (next [f] ⊛ x))) (⟦weak0⟧ f)

ifz-abs-θ-lemma : ∀ {Γ γ τ} {r : ▹ ⟦ nat ⟧t} (t0' t1' : Γ ⊢ τ)
                → let t0 = weak0 t0' ; t1 = weak0 t1' in
                ⟦ abs (ifz (var Z) then t0 else t1) ⟧ γ (future r)
                ≡ θ' (next (⟦ abs (ifz (var Z) then t0 else t1) ⟧ γ) ⊛ r)
ifz-abs-θ-lemma {Γ} {γ} {τ} {r} t0' t1' = 
  ⟦ abs (ifz (var Z) then t0 else t1) ⟧ γ (future r)
      ≡⟨ ? ⟩
  -- (λ (α :  ⟦ nat ⟧t) → ⟦ ifz (var Z) then t0 else t1 ⟧ p⟨ γ , α ⟩) (future r)
  --     ≡⟨⟩
  -- (λ (α :  ⟦ nat ⟧t) → map-ext ▹alg' (ifz' α) (⟦ var {Γ , nat} Z ⟧ p⟨ γ , α ⟩)) (future r)
  --     ≡⟨⟩
  -- (λ (α :  ⟦ nat ⟧t) → map-ext ▹alg' (ifz' α) α) (future r)
  --     ≡⟨⟩
  -- (λ (α :  ⟦ nat ⟧t) → gfix (map-ext-body ▹alg' (ifz' α)) α) (future r)
  --     ≡⟨ funExt (λ β → gfix-unfold (map-ext-body ▹alg' (ifz' β)) ≡$ β) ≡$ future r ⟩
  -- (λ (α :  ⟦ nat ⟧t) → map-ext-body ▹alg' (ifz' α) (next (map-ext ▹alg' (ifz' α))) α) (future r)
  --     ≡⟨⟩
  -- map-ext-body ▹alg' (ifz' (future r)) (next (map-ext ▹alg' (ifz' (future r)))) (future r)
  --     ≡⟨⟩
  -- θ' (next (map-ext ▹alg' (ifz' (future r))) ⊛ r) -- so far so good
  --     ≡⟨ ? ⟩
  -- θ' (next (λ (α : ⟦ nat ⟧t) → map-ext ▹alg' (ifz' α) α) ⊛ r)
  --     ≡⟨⟩
  -- θ' (next (λ (α : ⟦ nat ⟧t) → map-ext ▹alg' (ifz' α) (⟦ var {Γ , nat} Z ⟧ p⟨ γ , α ⟩)) ⊛ r)
  --     ≡⟨⟩
  -- θ' (next (λ (α : ⟦ nat ⟧t) → ⟦ ifz (var Z) then t0 else t1 ⟧ p⟨ γ , α ⟩) ⊛ r)
  --     ≡⟨⟩
  θ' (next (⟦ abs (ifz (var Z) then t0 else t1) ⟧ γ) ⊛ r) ∎
  where
    t0 = weak0 {Γ} {nat} t0'
    t1 = weak0 {Γ} {nat} t1'
    ifz' = λ (α : ⟦ nat ⟧t) → nat-ifz (⟦ t0 ⟧ p⟨ γ , α ⟩) (⟦ t1 ⟧ p⟨ γ , α ⟩)

{-

ifz-abs-θ-lemma : ∀ {Γ γ τ} {r : ▹ ⟦ nat ⟧t} (t0 t1 : Γ , nat ⊢ τ)
                → ⟦ abs (ifz (var Z) then t0 else t1) ⟧ γ (future r) ≡ θ' (next (⟦ abs (ifz (var Z) then t0 else t1) ⟧ γ) ⊛ r)
ifz-abs-θ-lemma {Γ} {γ} {τ} {r} t0 t1 =
        ≡⟨⟩
    map-ext ▹alg-⟦ τ ⟧t ifz (future r)
        ≡⟨ map-ext-clause ▹alg-⟦ τ ⟧t ifz r ⟩
    θₜ (next (map-ext ▹alg-⟦ τ ⟧t ifz) ⊛ r)
        ≡⟨ cong (λ - → θₜ (next -)) {! !} ⟩
    θₜ (next (λ α → ⟦ ifz (var Z) then t0 else t1 ⟧ ⟨ γ , α ⟩) ⊛ r)
        ≡⟨⟩
    θₜ (next (⟦ abs (ifz (var Z) then t0 else t1) ⟧ γ) ⊛ r) ∎
  where
    α = future r
    γ' = ⟨ γ , α ⟩

    θₜ = θ' {τ}

    ifz : Nat → ⟦ τ ⟧t
    ifz = nat-ifz (⟦ t0 ⟧ γ') (⟦ t1 ⟧ γ')

    helper : (λ α → map-ext ▹alg' (nat-ifz (⟦ t0 ⟧ ⟨ γ , α ⟩) (⟦ t1 ⟧ ⟨ γ , α ⟩)) α)
           ≡ ⟦ abs (ifz (var Z) then t0 else t1) ⟧ γ
    helper = funExt λ { α →
      map-ext ▹alg' (nat-ifz (⟦ t0 ⟧ ⟨ γ , α ⟩) (⟦ t1 ⟧ ⟨ γ , α ⟩)) α
        ≡⟨⟩
      ⟦ abs (ifz (var Z) then t0 else t1) ⟧ γ α
        ≡⟨⟩
      ⟦ ifz (var Z) then t0 else t1 ⟧ ⟨ γ , α ⟩ ∎ }

-}

{-


-}

-}
