module Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Isomorphism using (_≃_; extensionality)
open import Isomorphism using (_≃_; extensionality; _⇔_)
open import Relations using (_<_)
open import Connectives using (→-distrib-⊎)

¬_ : Set → Set
¬ A = A → ⊥

infix 3 ¬_

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
  → ⊥
¬-elim ¬x x = ¬x x

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x ¬x = ¬x x

¬¬¬-intro′ : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-intro′ ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
_≢_ x y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id = λ z → z

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality λ()

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ x → ⊥-elim (¬x x)

open _<_

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s x) = <-irreflexive x

suc-≡ : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-≡ suc≡ = cong (λ x → x ∸ 1) suc≡

data Tri (m n : ℕ) : Set where
  forward : (m < n) × ¬ (m ≡ n) × ¬ (n < m) → Tri m n

  fixed : ¬ (m < n) × (m ≡ n) × ¬ (n < m) → Tri m n

  flipped : ¬ (m < n) × ¬ (m ≡ n) × (n < m) → Tri m n

trichotomy : ∀ (m n : ℕ) → Tri m n
trichotomy zero zero = fixed ((λ ()) , refl , (λ ()))
trichotomy zero (suc n) = forward (z<s , (λ ()) , (λ ()))
trichotomy (suc m) zero = flipped ((λ ()) , (λ ()) , z<s)
trichotomy (suc m) (suc n) with trichotomy m n
... | forward (m<n , ¬m≡n , ¬n<m)
  = forward (s<s m<n , (λ x → ¬m≡n (suc-≡ x)) , λ{ (s<s n<m) → ¬n<m n<m})
... | flipped (¬m<n , ¬m≡n , n<m)
  = flipped ((λ{ (s<s m<n) → ¬m<n m<n }) , (λ x → ¬m≡n (suc-≡ x)) , s<s n<m)
... | fixed (¬m<n , m≡n , ¬n<m)
  = fixed ((λ{ (s<s m<n) → ¬m<n m<n }) , cong suc m≡n , λ{ (s<s n<m) → ¬n<m n<m})

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ ¬ A × ¬ B
⊎-dual-× = →-distrib-⊎

¬⊎-implies-¬× : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
¬⊎-implies-¬× =
  λ{ (inj₁ ¬a) → λ x → ¬a (proj₁ x)
   ; (inj₂ ¬b) → λ x → ¬b (proj₂ x)
   }

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ (λ x → k (inj₁ x)))

em-implies-¬¬-elim :
    (∀ {A : Set} → (A ⊎ ¬ A))
    -------------------------
  → ∀ {A′ : Set} → (¬ ¬ A′ → A′)
em-implies-¬¬-elim lem {A′} with lem {A′}
... | inj₁ a = λ _ → a
... | inj₂ ¬a = λ x → ⊥-elim (x ¬a)

¬¬-elim-implies-pierce :
    (∀ {A : Set} → (¬ ¬ A → A))
    -------------------------------------
  → ∀ {A′ B : Set} → ((A′ → B) → A′) → A′
¬¬-elim-implies-pierce elim {A′}
  = λ x → elim {A′} λ ¬a → (contraposition x) ¬a λ a → ⊥-elim (¬a a)

¬¬-elim-implies-pierce′ :
    (∀ {A : Set} → (¬ ¬ A → A))
    -------------------------------------
  → ∀ {A′ B : Set} → ((A′ → B) → A′) → A′
¬¬-elim-implies-pierce′ elim {A′} =
  λ x → elim {A′} λ ¬a → ¬a (x λ a → elim (λ _ → ¬a a)) -- ???

pierce-implies-→⊎ :
    (∀ {A B : Set} → ((A → B) → A) → A)
    -----------------------------------
  → ∀ {A′ B′ : Set} → (A′ → B′) → ¬ A′ ⊎ B′
pierce-implies-→⊎ pierce = λ a→b → pierce λ x → inj₁ λ a → x (inj₂ (a→b a))

Stable : Set → Set
Stable A = ¬ ¬ A → A

neg-stable : ∀ {A : Set} → Stable (¬ A)
neg-stable = λ ¬¬¬a a → (¬¬¬-elim ¬¬¬a) a

×-stable : ∀ {A B : Set}
  → Stable A
  → Stable B
  -----------------
  → Stable (A × B)
×-stable sa sb = λ ¬¬ab →
    sa (λ ¬a → ¬¬ab λ ab → ¬a (proj₁ ab))
  , sb λ ¬b → ¬¬ab λ ab → ¬b (proj₂ ab)

