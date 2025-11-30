module Term where

open import Agda.Builtin.Nat

infixl 5 _,_
infix  4 _∋_
infix  4 _⊢_
infixr 7 _⇒_
infixl 7 _∙_
infix  9 #_
infix  8 ifz_then_else_

data Type : Set where
  ⋆   : Type
  nat : Type
  _⇒_ : Type → Type → Type

variable τ τ₁ τ₂ τ₃ : Type

data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Type → Ctx

variable Γ Δ Ω : Ctx

_ : Ctx
_  = ∅ , ⋆ , (⋆ ⇒ ⋆) -- a context containing a variable of type ⋆ and a variable of type ⋆ ⇒ ⋆

-- Proof that a variable of a type is in a Context/the deBrujin index
data _∋_ : Ctx → Type → Set where
  Z : Γ , τ ∋ τ
  S_ : Γ ∋ τ₁ → Γ , τ ∋ τ₁

-- Intrinsically-typed terms
data _⊢_ : Ctx → Type → Set where
  var : Γ ∋ τ
      → Γ ⊢ τ
  _∙_ : Γ ⊢ τ₁ ⇒ τ₂
      → Γ ⊢ τ₁
      → Γ ⊢ τ₂
  abs : Γ , τ₁ ⊢ τ₂
      → Γ ⊢ τ₁ ⇒ τ₂

  #_  : Nat → Γ ⊢ nat
  pred : Γ ⊢ nat → Γ ⊢ nat
  succ : Γ ⊢ nat → Γ ⊢ nat
  ifz_then_else_ : Γ ⊢ nat → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ
  Y   : Γ ⊢ τ ⇒ τ → Γ ⊢ τ
