open import LaterPrims

module Denotation.LaterAlgebra where

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

