open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Cubical.Foundations.Prelude using (_∙_; sym)


infixr 5 _×_
record _×_ (A : Set) (B : Set) : Set where
  constructor pair
  field
    pfst : A
    psnd : B

data ⊥ : Set where
absurd : ∀ {l} {A : Set l} → ⊥ → A
absurd ()

∃₂ : {A B : Set} (P : A → B → Set) → Set
∃₂ {A} {B} P = Σ (A × B) λ { (pair x y) → P x y }

-- congruence without universe polymorphism

cong : ∀ {A B : Set} (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f eq = λ i → f (eq i)

cong₂ : ∀ {A B C : Set} (f : A → B → C) → {x x' : A} {y y' : B}
      → x ≡ x' → y ≡ y'
      → f x y ≡ f x' y'
cong₂ f eqx eqy = λ i → f (eqx i) (eqy i)

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) → {x x' : A} {y y' : B} {z z' : C}
      → x ≡ x' → y ≡ y' → z ≡ z'
      → f x y z ≡ f x' y' z'
cong₃ f eqx eqy eqz = λ i → f (eqx i) (eqy i) (eqz i)

≡-confluent : ∀ {A : Set} {x y z : A}
            → x ≡ y
            → x ≡ z
            → y ≡ z
≡-confluent x=y y=z = sym x=y ∙ y=z

nat-pred : Nat → Nat
nat-pred zero = 0
nat-pred (suc n) = n

nat-succ : Nat → Nat
nat-succ = suc
