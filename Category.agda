{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Axiom.Extensionality.Propositional

import Function as Fun

postulate
  ext : Extensionality _ _

record Category : Set where
  eta-equality

  field
    Obj : Set
    Hom : Obj -> Obj -> Set

  field
    id  : ∀ {A} → Hom A A
    comp : ∀ {A B C} → Hom A B → Hom B C → Hom A C

  field -- laws
    assoc     : ∀ {A B C D} {f : Hom A B} {g : Hom B C}{h : Hom C D} →
                comp f (comp g h) ≡ (comp (comp f g) h)
    identityˡ : ∀ {A B} {f : Hom A B} → comp id f ≡ f
    identityʳ : ∀ {A B} {f : Hom A B} → comp f id ≡ f
open Category

record Functor (C D : Category) : Set where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    act : C.Obj → D.Obj
    fmap : ∀ {X Y} (f : C.Hom X Y) → D.Hom (act X) (act Y)

  field -- laws
    identity     : ∀ {X} → fmap (C.id {X}) ≡ D.id {act X}
    homomorphism : ∀ {X Y Z} {f : C.Hom X Y}{g : C.Hom Y Z} →
                   fmap (C.comp f g) ≡ D.comp (fmap f) (fmap g)
open Functor

record NaturalTransformation {C D : Category}
                             (F G : Functor C D) : Set where
  eta-equality
  private
    module F = Functor F
    module G = Functor G
    module C = Category C
    module D = Category D

  field
    transform   : ∀ X → D.Hom (F.act X) (G.act X)
    natural     : ∀ X Y (f : C.Hom X Y) →
                  D.comp (F.fmap f) (transform Y) ≡ D.comp (transform X) (G.fmap f)
open NaturalTransformation

-- category of sets

SET : Category
SET = record
  { Obj = Set
  ; Hom = λ a b → a → b
  ; id  = Fun.id
  ; comp = λ f g x → g (f x)
  ; assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  }
