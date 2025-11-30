open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Cubical.Path

open import Cubical.Foundations.Prelude hiding (Type; _,_; _∙_)

open import LaterPrims
open import Term
open import Renaming

record _×_ (A : Set) (B : Set) : Set where
  constructor p⟨_,_⟩
  field
    proj0 : A
    proj1 : B

data 𝓛 (A : Set) : Set where
  now : A → 𝓛 A
  future : ▹ 𝓛 A → 𝓛 A

𝓛-map : {A B : Set} (f : A → B) → 𝓛 A → 𝓛 B
𝓛-map f (now a) = now (f a)
𝓛-map f (future r) = future λ { x → 𝓛-map f (r x) }

record ▹algebra (A : Set) : Set where
  constructor pack
  field
    θ : ▹ A → A

δ : {A : Set} → ▹algebra A → A → A
δ (pack θ) x = θ (next x)

▹alg-free : {A : Set} → ▹algebra (𝓛 A)
▹alg-free = pack future

▹alg-fun : {A B : Set} (lb : ▹algebra B) → ▹algebra (A → B)
▹alg-fun (pack θb) = pack λ { f x → θb (f ⊛ (next x)) }

map-ext-body : ∀ {A B} (lb : ▹algebra B) (f : A → B) → ▹ (𝓛 A → B) → 𝓛 A → B
map-ext-body _ f f' (now a) = f a
map-ext-body (pack θ) f f' (future r) = θ (f' ⊛ r)

map-ext : ∀ {A B} (lb : ▹algebra B) (f : A → B) → 𝓛 A → B
map-ext lb f = gfix (map-ext-body lb f)

⟦_⟧t : Type → Set
⟦ ⋆ ⟧t = 𝓛 ⊤
⟦ nat ⟧t = 𝓛 Nat
⟦ σ ⇒ τ ⟧t = ⟦ σ ⟧t → ⟦ τ ⟧t

▹alg-⟦_⟧t : (τ : Type) → ▹algebra ⟦ τ ⟧t
▹alg-⟦ ⋆ ⟧t = ▹alg-free
▹alg-⟦ nat ⟧t = ▹alg-free
▹alg-⟦ σ ⇒ τ ⟧t = ▹alg-fun ▹alg-⟦ τ ⟧t

▹alg' : {τ : Type} → ▹algebra ⟦ τ ⟧t
▹alg' = ▹alg-⟦ _ ⟧t

θ' : {τ : Type} → ▹ ⟦ τ ⟧t → ⟦ τ ⟧t
θ' = let pack θ = ▹alg-⟦ _ ⟧t in θ

δ' : {τ : Type} → ⟦ τ ⟧t → ⟦ τ ⟧t
δ' x = θ' (next x)

⟦_⟧c : Ctx → Set
⟦ ∅ ⟧c = ⊤
⟦ Γ , σ ⟧c = ⟦ Γ ⟧c × ⟦ σ ⟧t

env-lookup : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧c → ⟦ τ ⟧t
env-lookup Z p⟨ γ , α ⟩ = α
env-lookup (S x) p⟨ γ , α ⟩ = env-lookup x γ

nat-pred : Nat → Nat
nat-pred zero = 0
nat-pred (suc n) = n

nat-succ : Nat → Nat
nat-succ = suc

nat-ifz : ∀ {A : Set} (x y : A) (n : Nat) → A
nat-ifz t0 t1 zero = t0
nat-ifz t0 t1 (suc n) = t1

⟦_⟧ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧c → ⟦ τ ⟧t
⟦ var x ⟧ γ = env-lookup x γ
⟦ f ∙ t ⟧ γ = ⟦ f ⟧ γ (⟦ t ⟧ γ)
⟦ abs t ⟧ γ = λ α → ⟦ t ⟧ p⟨ γ , α ⟩
⟦ # n ⟧ γ = now n
⟦ pred t ⟧ γ = 𝓛-map nat-pred (⟦ t ⟧ γ)
⟦ succ t ⟧ γ = 𝓛-map nat-succ (⟦ t ⟧ γ)
⟦ ifz e then t0 else t1 ⟧ γ = map-ext ▹alg' (nat-ifz (⟦ t0 ⟧ γ) (⟦ t1 ⟧ γ)) (⟦ e ⟧ γ)
⟦ Y f ⟧ γ = gfix (λ x → θ' (next (⟦ f ⟧ γ) ⊛ x))

Y-delay : ∀ {Γ γ τ} (f : Γ ⊢ τ ⇒ τ)
        → ⟦ Y f ⟧ γ ≡ δ' (⟦ f ∙ (Y f) ⟧ γ)
Y-delay {_} {γ} {_} f =
    ⟦ Y f ⟧ γ
        ≡⟨⟩
    gfix (λ x → θ' (next (⟦ f ⟧ γ) ⊛ x))
        ≡⟨ (gfix-unfold λ { x → θ' (next (⟦ f ⟧ γ) ⊛ x) }) ⟩
    θ' (next (⟦ f ⟧ γ) ⊛ next (⟦ Y f ⟧ γ))
        ≡⟨⟩
    θ' (next ((⟦ f ⟧ γ) (⟦ Y f ⟧ γ)))
        ≡⟨⟩
    δ' (⟦ f ∙ (Y f) ⟧ γ) ∎

weak0 : ∀ {Γ τ σ} → Γ ⊢ σ → Γ , τ ⊢ σ
weak0 e = suc-renaming (idᴿ _) ⟪ e ⟫

data _===_ {A : Set} (x : A) : A → Set where
  eq-refl : x === x
{-# BUILTIN EQUALITY _===_ #-}

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
⟦weak0⟧ (f ∙ t) {γ} {β} = cong₂ (λ x y → x y) (⟦weak0⟧ f) (⟦weak0⟧ t)
⟦weak0⟧ (abs e) = {! !}
⟦weak0⟧ (# n) = refl
⟦weak0⟧ (pred e) = cong (𝓛-map nat-pred) (⟦weak0⟧ e)
⟦weak0⟧ (succ e) = cong (𝓛-map nat-succ) (⟦weak0⟧ e)
⟦weak0⟧ (Y e) = cong (λ s → gfix (λ x → θ' (next s ⊛ x))) (⟦weak0⟧ e)
⟦weak0⟧ (ifz e then t₀ else t₁) {γ} {β} =
    ⟦ weak0 (ifz e then t₀ else t₁) ⟧ p⟨ γ , β ⟩
        ≡⟨⟩
    ⟦ ifz weak0 e then weak0 t₀ else weak0 t₁ ⟧ p⟨ γ , β ⟩
        ≡⟨⟩
    map-ext ▹alg' (nat-ifz (⟦ weak0 t₀ ⟧ p⟨ γ , β ⟩) (⟦ weak0 t₁ ⟧ p⟨ γ , β ⟩)) (⟦ weak0 e ⟧ p⟨ γ , β ⟩)
        ≡⟨ cong (λ s → map-ext ▹alg' (nat-ifz (⟦ weak0 t₀ ⟧ p⟨ γ , β ⟩) (⟦ weak0 t₁ ⟧ p⟨ γ , β ⟩)) s) (⟦weak0⟧ e) ⟩
    map-ext ▹alg' (nat-ifz (⟦ weak0 t₀ ⟧ p⟨ γ , β ⟩) (⟦ weak0 t₁ ⟧ p⟨ γ , β ⟩)) (⟦ e ⟧ γ)
        ≡⟨ cong₂ (λ x y → map-ext ▹alg' (nat-ifz x y) (⟦ e ⟧ γ)) (⟦weak0⟧ t₀) (⟦weak0⟧ t₁) ⟩
    map-ext ▹alg' (nat-ifz (⟦ t₀ ⟧ γ) (⟦ t₁ ⟧ γ)) (⟦ e ⟧ γ)
        ≡⟨⟩
    ⟦ ifz e then t₀ else t₁ ⟧ γ ∎

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

ifz-delta-comm : ∀ {Γ γ τ} (n n' : Γ ⊢ nat) (t0 t1 : Γ ⊢ τ)
               → ⟦ n ⟧ γ ≡ δ' {nat} (⟦ n' ⟧ γ)
               → ⟦ ifz n then t0 else t1 ⟧ γ ≡ δ' (⟦ ifz n' then t0 else t1 ⟧ γ)
ifz-delta-comm {_} {γ} {_} n n' t0 t1 eq = {!!}

-}

