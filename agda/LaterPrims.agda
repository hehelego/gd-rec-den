open import Agda.Primitive using (Level)
open import Agda.Builtin.Cubical.Path using (_≡_)

primitive
    primLockUniv : Set₁

private
  variable
    l1 : Level
    l2 : Level
    A : Set l1
    B : Set l2
    C : Set l2

postulate
  Tick : primLockUniv

▹_ : ∀ {l} → Set l → Set l
▹_ A = (@tick x : Tick) -> A

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

infixl 10 _⊛_

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)

postulate
  gfix : ∀ {l} {A : Set l} → (▹ A → A) → A
  gfix-unfold : ∀ {l} {A : Set l} (f : ▹ A → A) → gfix f ≡ f (next (gfix f))
