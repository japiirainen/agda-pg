module Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level)
open import Isomorphism using (_≃_; _⇔_; extensionality)
open import Inductions using (*-distrib-+; ∸-+-assoc; *-comm; +-comm)
open import Quantifiers using (∀-extensionality)
open import Data.Empty using (⊥; ⊥-elim)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎

++-assoc : ∀ {A : Set} → (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (_ ∷ xs) = suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎

reverse-++-distrib : ∀ {A : Set} → (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ []
  ≡⟨⟩
    reverse ys ++ reverse []
  ∎
reverse-++-distrib (x ∷ xs) ys =
  begin
    reverse (x ∷ xs ++ ys)
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

reverse-extract : ∀ {A : Set} (xs : List A) (x : A)
  → reverse (xs ++ [ x ]) ≡ x ∷ reverse xs
reverse-extract [] x = refl
reverse-extract (x ∷ xs) y = cong (_++ [ x ]) (reverse-extract xs y)

reverse-involutive : ∀ {A : Set} {xs : List A}
  → reverse (reverse xs) ≡ xs
reverse-involutive {A} {[]} = refl
reverse-involutive {A} {x ∷ xs} =
  begin
      reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-extract (reverse xs) x ⟩
      (x ∷ reverse (reverse xs))
  ≡⟨ cong (x ∷_) (reverse-involutive {A} {xs}) ⟩
      (x ∷ xs)
  ∎

shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎

map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C}
  → map (g ∘ f) ≡ map g ∘ map f
map-compose {A} {B} {C} {f} {g} = extensionality (lemma f g)
  where
    lemma : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A)
       → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    lemma f g [] = refl
    lemma f g (x ∷ xs) = cong ((g ∘ f) x ∷_) (lemma f g xs)

map-++-commute : ∀ {A B : Set} {f : A → B} {xs ys : List A}
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute {A} {B} {f} {[]} {ys} = refl
map-++-commute {A} {B} {f} {x ∷ xs} {ys} = 
  cong (f x ∷_) (map-++-commute {A} {B} {f} {xs} {ys})

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node t x t′) = node (map-Tree f g t) (g x) (map-Tree f g t′)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ b [] = b
foldr _⊗_ b (x ∷ xs) = x ⊗ foldr _⊗_ b xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎

product : List ℕ → ℕ
product = foldr _*_ 1

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys = cong (x ⊗_) (foldr-++ _⊗_ e xs ys)

map-is-foldr : ∀ {A B : Set} {f : A → B} →
  map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {A} {B} {f} = extensionality lemma
  where
    lemma : ∀ {A B : Set} {f : A → B} (xs : List A) →
      map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
    lemma [] = refl
    lemma {A} {B} {f} (x ∷ xs) = cong (f x ∷_) (lemma xs)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node t x t′) = g (fold-Tree f g t) x (fold-Tree f g t′)

map-is-fold-Tree : ∀ {A B C D : Set} {f : A → C} {g : B → D} →
  map-Tree f g ≡ fold-Tree {A} {B} {Tree C D} 
                 (λ x → leaf (f x))
                 (λ lf x rt → node lf (g x) rt)
map-is-fold-Tree = extensionality lemma
  where
    lemma : ∀ {A B C D : Set} {f : A → C} {g : B → D} (xs : Tree A B) →
      map-Tree f g xs ≡ fold-Tree {A} {B} {Tree C D}
                        (λ x → leaf (f x))
                        (λ lf x rt → node lf (g x) rt) xs
    lemma (leaf x) = refl
    lemma {A} {B} {C} {D} {f} {g} (node lf x rt)
                                  rewrite lemma {A} {B} {C} {D} {f} {g} lf
                                | lemma {A} {B} {C} {D} {f} {g} rt = refl

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid = 
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
assoc *-monoid = *-assoc
identityˡ *-monoid = *-identityˡ
identityʳ *-monoid = *-identityʳ

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ b [] = b
foldl _⊗_ b (x ∷ xs) = foldl _⊗_ (b ⊗ x) xs

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → y ⊗ foldl _⊗_ e xs ≡ foldl _⊗_ y xs
foldl-monoid _⊗_ e ⊗-monoid [] y = identityʳ ⊗-monoid y
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y
    rewrite identityˡ ⊗-monoid x
          | sym (foldl-monoid _⊗_ e ⊗-monoid xs x)
          | sym (assoc ⊗-monoid y x (foldl _⊗_ e xs))
           = foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x)

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) 
  → IsMonoid _⊗_ e
  → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl _⊗_ e ⊗-monoid = extensionality (lemma _⊗_ e ⊗-monoid)
  where
    lemma : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
      → ∀ (xs : List A)
      → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
    lemma _⊗_ e ⊗-monoid [] = refl
    lemma _⊗_ e ⊗-monoid (x ∷ xs)
      rewrite lemma _⊗_ e ⊗-monoid xs
            | foldl-monoid _⊗_ e ⊗-monoid xs x
            | identityˡ ⊗-monoid x
              = refl

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 2 , 3 ]
_ = here refl

_ : 0 ∈ [ 3 , 2 , 0 , 1 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      All P (xs ++ ys) → (All P xs × All P ys)
    to [] ys Pys = ⟨ [] , Pys ⟩
    to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
    ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

    from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
      All P xs × All P ys → All P (xs ++ ys)
    from [] ys ⟨ [] , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    to [] ys anyp = inj₂ anyp
    to (x ∷ xs) ys (here px) = inj₁ (here px)
    to (x ∷ xs) ys (there anyp) with to xs ys anyp
    ... | inj₁ anyx = inj₁ (there anyx)
    ... | inj₂ anyy = inj₂ anyy

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
    from _ _ (inj₁ (here ax)) = here ax
    from (x ∷ xs) ys (inj₁ (there ax)) = there (from xs ys (inj₁ ax))
    from [] ys (inj₂ y) = y
    from (x ∷ xs) ys (inj₂ y) = there (from xs ys (inj₂ y))

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    ; from∘to = from∘to xs ys
    ; to∘from = to∘from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      All P (xs ++ ys) → (All P xs × All P ys)
    to [] ys Pys = ⟨ [] , Pys ⟩
    to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
    ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

    from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
      All P xs × All P ys → All P (xs ++ ys)
    from [] ys ⟨ [] , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

    from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) (x : All P (xs ++ ys))
      → from xs ys (to xs ys x) ≡ x
    from∘to [] ys x = refl
    from∘to (x ∷ xs) ys (px ∷ allp) = cong (px ∷_) (from∘to xs ys allp)

    to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A) (y : All P xs × All P ys)
      → to xs ys (from xs ys y) ≡ y
    to∘from [] ys ⟨ [] , snd ⟩ = refl
    to∘from (x ∷ xs) ys ⟨ px ∷ fst , snd ⟩ rewrite to∘from xs ys ⟨ fst , snd ⟩ = refl

_∘′_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘′ f) x  =  g (f x)

¬Any≃All¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
  → (¬_ ∘′ Any P) xs ≃ All (¬_ ∘′ P) xs
¬Any≃All¬ P xs =
  record
    { to = to P xs
    ; from = from P xs
    ; from∘to = from∘to P xs
    ; to∘from = to∘from P xs
    }

  where

    to : ∀ {A : Set} (P : A → Set) (xs : List A)
      → (¬_ ∘′ Any P) xs → All (¬_ ∘′ P) xs
    to _ [] _ = []
    to P (x ∷ xs) ¬Any = (λ Px → ¬Any (here Px)) ∷ to P xs λ anyx → ¬Any (there anyx)

    from : ∀ {A : Set} (P : A → Set) (xs : List A)
      → All (¬_ ∘′ P) xs → (¬_ ∘′ Any P) xs
    from P [] [] ()
    from P (x ∷ xs) (¬Px ∷ All¬) (here Px) = ¬Px Px
    from P (x ∷ xs) (¬Px ∷ All¬) (there anyp) = from P xs All¬ anyp

    from∘to : ∀ {A : Set} (P : A → Set) (xs : List A) (x : (¬_ ∘′ Any P) xs)
      → from P xs (to P xs x) ≡ x
    from∘to P [] ¬Any = extensionality λ ()
    from∘to P (x ∷ xs) ¬Any = extensionality
      λ{ (here Px) → refl
       ; (there anyp) → ⊥-elim (¬Any (there anyp))
       }

    to∘from : ∀ {A : Set} (P : A → Set) (xs : List A) (y : All (¬_ ∘′ P) xs)
      → to P xs (from P xs y) ≡ y
    to∘from P [] [] = refl
    to∘from P (x ∷ xs) (¬Px ∷ All¬) = cong (¬Px ∷_) (to∘from P xs All¬)

Any¬-implies-¬All : ∀ {A : Set} (P : A → Set) (xs : List A)
  → Any (¬_ ∘′ P) xs → (¬_ ∘′ All P) xs
Any¬-implies-¬All P (x ∷ xs) (here ¬Px) (Px ∷ allp) = ¬Px Px
Any¬-implies-¬All P (x ∷ xs) (there Any¬) (Px ∷ allp) =
  Any¬-implies-¬All P xs Any¬ allp

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p = foldr _∧_ true ∘ map p

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P = ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 = yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     = yes (Px ∷ Pxs)
...                 | no ¬Px | _           = no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     = no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }

any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p = foldr _∨_ false ∘ map p

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no λ ()
Any? P? (x ∷ xs) with P? x | Any? P? xs 
...                 | yes Px | _         = yes (here Px)
...                 | _      | yes Pxs   = yes (there Pxs)
...                 | no ¬Px | no ¬Pxs  = no λ { (here Px) → ¬Px Px
                                               ; (there anyp) → ¬Pxs anyp 
                                               }

Any-∃ : ∀ {A : Set} (P : A → Set) (xs : List A)
  → Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃ {A} P xs =
  record
    { to = to xs
    ; from = from xs
    ; from∘to = from∘to xs
    ; to∘from = to∘from xs
    }

  where

    to : ∀ (xs : List A)
      → Any P xs → ∃[ x ] (x ∈ xs × P x)
    to (x ∷ xs) (here Px) = ⟨ x , ⟨ (here refl) , Px ⟩ ⟩
    to (x ∷ xs) (there anyp) with to xs anyp
    ... | ⟨ x′ , ⟨ x′∈xs , Px′ ⟩ ⟩ = ⟨ x′ , ⟨ (there x′∈xs) , Px′ ⟩ ⟩

    from : ∀ (xs : List A)
      → ∃[ x ] (x ∈ xs × P x) → Any P xs
    from (x ∷ xs) ⟨ x′ , ⟨ here x′≡x , Px′ ⟩ ⟩ rewrite sym x′≡x = here Px′
    from (x ∷ xs) ⟨ x′ , ⟨ there x′∈xs , Px′ ⟩ ⟩ =
      there (from xs ⟨ x′ , ⟨ x′∈xs , Px′ ⟩ ⟩)

    from∘to : ∀ (xs : List A) (x : Any P xs) → from xs (to xs x) ≡ x
    from∘to (x ∷ xs) (here Px) = refl
    from∘to (x ∷ xs) (there anyp) = cong there (from∘to xs anyp)

    to∘from : ∀ (xs : List A) (y : ∃[ x ] (x ∈ xs × P x)) → to xs (from xs y) ≡ y
    to∘from (x ∷ xs) ⟨ .x , ⟨ here refl , Px′ ⟩ ⟩ = refl
    to∘from (x ∷ xs) ⟨ x′ , ⟨ there x′∈xs , Px′ ⟩ ⟩ =
      cong (λ{ ⟨ x″ , ⟨ x″∈xs , Px″ ⟩ ⟩ → ⟨ x″ , ⟨ (there x″∈xs) , Px″ ⟩ ⟩})
        (to∘from xs ⟨ x′ , ⟨ x′∈xs , Px′ ⟩ ⟩)

filter? : ∀ {A : Set} {P : A → Set}
  → (P? : Decidable P) → List A → ∃[ ys ]( All P ys )
filter? P? [] = ⟨ [] , [] ⟩
filter? P? (x ∷ xs) with P? x   | filter? P? xs
...                    | yes Px | ⟨ ys , allys ⟩ = ⟨ x ∷ ys , Px ∷ allys ⟩
...                    | no  _  | ∃ys            = ∃ys

not? : (x : Bool) → Dec (x ≡ false)
not? false = yes refl
not? true = no λ ()

_ : filter? not? [ true , false , true , true , false ]
  ≡ ⟨ [ false , false ] , refl ∷ refl ∷ [] ⟩
_ = refl
