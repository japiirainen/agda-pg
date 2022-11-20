data Term : Set where
  true  : Term
  false : Term
  if_then_else_end : Term → Term → Term → Term

data Value : Term → Set where
  true  : Value true
  false : Value false

-- Small-step evaluation rules for the `arith` language
data _⟶_ : Term → Term → Set where
  E-IfTrue : ∀ {t₂ t₃} →
    --------------------------------
    if true then t₂ else t₃ end ⟶ t₂

  E-IfFalse : ∀ {t₂ t₃} →
    --------------------------------
    if false then t₂ else t₃ end ⟶ t₃

  E-If : ∀ {t₁ t₁' t₂ t₃} →
    t₁ ⟶ t₁' →
    ------------------------------------------------------
    if t₁ then t₂ else t₃ end ⟶ if t₁' then t₂ else t₃ end

