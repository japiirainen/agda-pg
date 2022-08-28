module Lambda where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Isomorphism using (_≲_; _≃_; extensionality)

Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _∙_
infix  8  `suc_
infix  9  `_


data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _∙_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" ∙ ` "m" ∙ ` "n") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" ∙ (` "s" ∙ ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
        ` "m" ∙ ` "s" ∙ (` "n" ∙ ` "s" ∙ ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ `zero
          |suc "m" ⇒ plus ∙ ` "n" ∙ ( ` "*" ∙ ` "m" ∙ ` "n" ) ]

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" ∙ ( ƛ "x" ⇒ plusᶜ ∙ ` "n" ∙ ` "x" ∙ ` "s" ∙ ` "z" ) ∙ ` "z"

ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
ƛ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
μ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ ∙ m ∙ n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
        case′ m
          [zero⇒ `zero
          |suc m ⇒ plus ∙ n ∙ ( * ∙ m ∙ n ) ]
  where
  *  =  ` "*"
  m  =  ` "m"
  n  =  ` "n"

data Value : Term → Set where
  V-ƛ : ∀ {x N}
    → Value (ƛ x ⇒ N)

  V-zero : Value `zero

  V-suc : ∀ {V}
    → Value V
    → Value (`suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  ƛ x ⇒ N
... | no  _          =  ƛ x ⇒ N [ y := V ]
(L ∙ M) [ y := V ]   =  L [ y := V ] ∙ M [ y := V ]
(`zero) [ y := V ]   =  `zero
(`suc M) [ y := V ]  =  `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  μ x ⇒ N
... | no  _          =  μ x ⇒ N [ y := V ]

_[_:=_]′ : Term → Id → Term → Term

subsIf : Id → Term → Id → Term → Term
subsIf y V x N with x ≟ y
... | yes _          =  N
... | no  _          =  N [ y := V ]′

(` x) [ y := V ]′ with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ]′ = ƛ x ⇒ subsIf y V x N
(L ∙ M) [ y := V ]′   =  L [ y := V ]′ ∙ M [ y := V ]′
(`zero) [ y := V ]′   =  `zero
(`suc M) [ y := V ]′  =  `suc M [ y := V ]′
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ]′
    =  case L [ y := V ]′ [zero⇒ M [ y := V ]′ |suc x ⇒ subsIf y V x N ]
(μ x ⇒ N) [ y := V ]′ = μ x ⇒ ( subsIf y V x N )

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L ∙ M —→ L′ ∙ M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V ∙ M —→ V ∙ M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) ∙ V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

—↠-trans : ∀ {M L N} → M —↠ L → L —↠ N → M —↠ N
—↠-trans (_ ∎) M—↠N = M—↠N
—↠-trans {M} {L} {N} (_ —→⟨ M—↠LL ⟩ LL—↠L) L—↠N =
  M —→⟨ M—↠LL ⟩ —↠-trans LL—↠L L—↠N

one : Term
one = `suc `zero

_ : plus ∙ one ∙ one —↠ two
_ =
  begin
    plus ∙ one ∙ one
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus ∙ ` "m" ∙ ` "n") ])
         ∙ one ∙ one
  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "n" ⇒
      case one [zero⇒ ` "n" |suc "m" ⇒ `suc (plus ∙ ` "m" ∙ ` "n") ])
         ∙ one
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    case one [zero⇒ one |suc "m" ⇒ `suc (plus ∙ ` "m" ∙ one) ]
  —→⟨ β-suc V-zero ⟩
    `suc (plus ∙ `zero ∙ one)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus ∙ ` "m" ∙ ` "n") ])
         ∙ `zero ∙ one)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
    `suc ((ƛ "n" ⇒
       case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus ∙ ` "m" ∙ ` "n") ])
      ∙ one)
  —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
    `suc (
       case `zero [zero⇒ one |suc "m" ⇒ `suc (plus ∙ ` "m" ∙ one) ])
  —→⟨ ξ-suc β-zero ⟩
    `suc one
  ∎

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

Context-≃ : Context ≃ List (Id × Type)
Context-≃ =
  record
    { to = to
    ; from = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }

  where

    to : Context → List (Id × Type)
    to ∅ = []
    to (Γ , var ⦂ type) = ⟨ var , type ⟩ ∷ to Γ

    from : List (Id × Type) → Context
    from [] = ∅
    from (⟨ var , type ⟩ ∷ xs) = from xs , var ⦂ type

    from∘to : ∀ (x : Context) → from (to x) ≡ x
    from∘to ∅ = refl
    from∘to (Γ , var ⦂ type) rewrite from∘to Γ = refl

    to∘from : ∀ (y : List (Id × Type)) → to (from y) ≡ y
    to∘from [] = refl
    to∘from (⟨ var , type ⟩ ∷ xs) rewrite to∘from xs = refl

infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L ∙ M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ
  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A

_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y  with x ≟ y
...       | no  x≢y  =  x≢y
...       | yes _    =  ⊥-elim impossible
  where postulate impossible : ⊥
