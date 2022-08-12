module HuttonsRazor where

open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Maybe hiding (decToMaybe)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

infixl 4 _+E_
infix 0 ifE_then_else_

data Expr : Set where
  num            : ℕ → Expr
  bit            : Bool → Expr
  _+E_           : Expr → Expr → Expr
  ifE_then_else_ : Expr → Expr → Expr → Expr

e1 : Expr
e1 = num 7 +E num 3 +E num 10

e2 : Expr
e2 = (ifE bit true then num 2 else num 4) +E num 0

ne3 : Expr
ne3 = ifE num 6 then bit false else bit true

data Val : Set where
  num : ℕ → Val
  bit : Bool → Val

_+V_ : Val → Val → Maybe Val
num a +V num b = just (num (a + b))
_ +V _ = nothing

eval : Expr → Maybe Val
eval (num n) = just (num n)
eval (bit b) = just (bit b)
eval (e +E e′) = do
  v₁ ← eval e
  v₂ ← eval e′
  v₁ +V v₂
eval (ifE e then e′ else e′′) = do
  (bit b) ← eval e where _ → nothing
  if b then eval e′ else eval e′′

_ : eval e1 ≡ just (num 20)
_ = refl

_ : eval e2 ≡ just (num 2)
_ = refl

_ : eval ne3 ≡ nothing
_ = refl

data Ty : Set where
  nat  : Ty
  bool : Ty

data TExpr : Ty → Set where
  num            : ℕ → TExpr nat
  bit            : Bool → TExpr bool
  _+E_           : TExpr nat → TExpr nat → TExpr nat
  ifE_then_else_ : ∀ {t} → TExpr bool → TExpr t → TExpr t → TExpr t
  

te1 : TExpr nat
te1 = num 7 +E num 3 +E num 10

te2 : TExpr nat
te2 = (ifE bit true then num 2 else num 4) +E num 0

-- This is not incorrect by construction !
-- tne3 : TExpr ?
-- tne3 = ifE num 6 then bit false else bit true

TVal : Ty → Set
TVal nat  = ℕ
TVal bool = Bool

teval : ∀ {t} → TExpr t → TVal t
teval (num n)   = n
teval (bit b)   = b
teval (e +E e′) = teval e + teval e′
teval (ifE e then e′ else e′′) =
  if teval e then teval e′ else teval e′′

_ : teval te1 ≡ 20
_ = refl

_ : teval te2 ≡ 2
_ = refl

∣_∣  : ∀ {t} → TExpr t -> Expr
∣ num n ∣ = num n
∣ bit b ∣ = bit b
∣ e +E e' ∣ = ∣ e ∣ +E ∣ e' ∣
∣ ifE e then e' else e'' ∣ = ifE ∣ e ∣ then ∣ e' ∣ else ∣ e'' ∣

record Welltyped (e : Expr) : Set where
  constructor okay
  field
   τ : Ty
   t : TExpr τ
   is-same : ∣ t ∣ ≡ e

_≟′_ : (τ : Ty) -> (τ′ : Ty) -> Dec (τ ≡ τ′)
nat ≟′ nat = yes refl
nat ≟′ bool = no (λ ())
bool ≟′ nat = no (λ ())
bool ≟′ bool = yes refl

decToMaybe : {P : Set} -> Dec P -> Maybe P
decToMaybe (yes p) = just p
decToMaybe (no p)  = nothing

_≟_ : (τ : Ty) -> (τ′ : Ty) -> Maybe (τ ≡ τ′)
x ≟ y = decToMaybe (x ≟′ y)

infer : (e : Expr) → Maybe (Welltyped e)
infer (num n)   = just (okay nat (num n) refl)
infer (bit b)   = just (okay bool (bit b) refl)
infer (e +E e′) = do
  okay nat t p ← infer e where _ → nothing
  okay nat t′ p′ ← infer e′ where _ → nothing
  just (okay nat (t +E t′) (cong₂ _+E_ p p′))
infer (ifE e then e′ else e′′) = do
  okay bool t refl ← infer e where _ → nothing
  okay τ t′ refl ← infer e′
  okay τ′ t′′ refl ← infer e′′
  refl ← τ ≟ τ′
  just (okay τ (ifE t then t′ else t′′) refl)

∣_∣V : ∀ {t} → TVal t → Val
∣_∣V {nat} = num
∣_∣V {bool} = bit

eval′ : Expr → Maybe Val
eval′ e = do
  okay _ t _ ← infer e
  just ∣ teval t ∣V

_ : eval′ e1 ≡ just (num 20)
_ = refl

_ : eval′ e2 ≡ just (num 2)
_ = refl

_ : eval′ ne3 ≡ nothing
_ = refl

-- ----------------------
-- Optimizing expressions
-- ----------------------

cfold : ∀ {t} → TExpr t → TExpr t
cfold (num x) = num x
cfold (bit x) = bit x
cfold (e +E e′) with cfold e | cfold e′
... | num n | num n′ = num (n + n′)
... | ce    | ce′    = ce +E ce′
cfold (ifE e then e′ else e′′) =
 ifE cfold e then cfold e′ else cfold e′′

_ : cfold te1 ≡ num 20
_ = refl

-- Proof that the cfold optimization is correct
cfold-sound : ∀ {t} → (e : TExpr t) -> teval (cfold e) ≡ teval e
cfold-sound (num x) = refl
cfold-sound (bit x) = refl
cfold-sound (e +E e') with cfold e | cfold e' | cfold-sound e | cfold-sound e'
... | num n | num n' | p | q = cong₂ _+_ p q
... | num x | ce' +E ce'' | p | q = cong₂ _+_ p q
... | num x | ifE ce' then ce'' else ce''' | p | q = cong₂ _+_ p q
... | ce +E ce₁ | num x | p | q = cong₂ _+_ p q
... | ce +E ce₁ | ce' +E ce'' | p | q = cong₂ _+_ p q
... | ce +E ce₁ | ifE ce' then ce'' else ce''' | p | q = cong₂ _+_ p q
... | ifE ce then ce₁ else ce₂ | num x | p | q = cong₂ _+_ p q
... | ifE ce then ce₁ else ce₂ | ce' +E ce'' | p | q = cong₂ _+_ p q
... | ifE ce then ce₁ else ce₂ | ifE ce' then ce'' else ce''' | p | q = cong₂ _+_ p q
cfold-sound(ifE e then e' else e'') rewrite cfold-sound e
                                  | cfold-sound e' 
                                  | cfold-sound e'' = refl

data Zeroness : (e e′ : TExpr nat) → Set where
  both : Zeroness (num 0) (num 0)
  left : (e′ : TExpr nat) → Zeroness (num 0) e′
  right : (e : TExpr nat) → Zeroness e (num 0)
  neither : (e e′ : TExpr nat) → Zeroness e e′

zeroness : (e e′ : TExpr nat) → Zeroness e e′
zeroness (num 0) (num 0) = both
zeroness (num 0) e′ = left e′
zeroness e (num 0) = right e
zeroness e e′ = neither e e′

remove+0 : ∀ {t} → TExpr t → TExpr t
remove+0 (num x) = num x
remove+0 (bit x) = bit x
remove+0 (e +E e′) with remove+0 e
                      | remove+0 e′ 
                      | zeroness (remove+0 e) (remove+0 e′)
... | _ | _ | both = num 0
... | _ | _ | left re′ = re′
... | _ | _ | right re = re
... | _ | _ | neither re re′ = re +E re′

remove+0 (ifE e then e₁ else e₂) =
  ifE remove+0 e then remove+0 e₁ else remove+0 e₂

te3 : TExpr nat
te3 = num 0 +E num 60 +E num 0 +E num 9

_ : remove+0 te3 ≡ (num 60 +E num 9)
_ = refl

_ : teval (remove+0 te3) ≡ teval te3
_ = refl

_ : teval te3 ≡ 69
_ = refl

remove+0-sound : ∀ {t} → (e : TExpr t) -> teval (remove+0 e) ≡ teval e
remove+0-sound (num x) = refl
remove+0-sound (bit x) = refl
remove+0-sound (e +E e') with remove+0 e
                            | remove+0 e'
                            | zeroness (remove+0 e) (remove+0 e')
                            | remove+0-sound e
                            | remove+0-sound e'
... | _ | _ | both | p | q rewrite sym p | sym q = refl
... | _ | _ | left _ | p | q rewrite sym p | sym q = refl
... | _ | _ | right _ | p | q rewrite sym p | sym q = sym (+-identityʳ _)
... | _ | _ | neither _ _ | p | q rewrite sym p | sym q = refl
remove+0-sound (ifE e then e' else e'')
  rewrite remove+0-sound e | remove+0-sound e' | remove+0-sound e'' = refl

