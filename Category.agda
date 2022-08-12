{-# OPTIONS --type-in-type #-}
module Category where

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs.WithK
import Function as Fun

record Category : Set where
  eta-equality
  infixr 9 _∘_

  field
    Obj : Set
    Hom : Obj → Obj → Set

  _⇒_ = Hom

  field
    id : ∀ {A} → (A ⇒ A)
    comp : ∀ {A B C} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C)

  _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
  f ∘ g = comp g f

  field
    assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → 
      (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f


record Functor (C D : Category) : Set where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    act : C.Obj → D.Obj
    fmap : ∀ {A B} (f : A C.⇒ B) → act A D.⇒ act B

  field -- laws
    identity : ∀ {A} → fmap (C.id {A}) ≡ D.id
    homomorpthism : ∀ {X Y Z} {f : X C.⇒ Y} {g : Y C.⇒ Z} →
      fmap (g C.∘ f) ≡ fmap g D.∘ fmap f

open Functor

----------------------------
-- The category of Sets
----------------------------

SET : Category
Category.Obj SET = Set
Category.Hom SET A B = A → B
Category.id SET = Fun.id
Category.comp SET f g = g Fun.∘′ f
Category.assoc SET = refl
Category.identityˡ SET = refl
Category.identityʳ SET = refl
