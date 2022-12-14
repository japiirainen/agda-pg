```agda
{-# OPTIONS --without-K --safe #-}

module lecture3 where

-- lecture 3
-- Plan: Complete last lecture.
--       Generalize some definitions to use universe levels.
--       Uses of Sigma, including examples like monoids.
--       Use of universes to prove that Â¬ (false â¡ true).
--       Characterization of equality in Î£ types.


open import lecture1 hiding (ð ; ð ; â ; D ; _â£_ ; â)
open import lecture2 using (is-prime ; _*_ ; ð ; ð ; â ; _â¥_)
open import introduction using (â ; zero ; suc ; _+_)

-- Give Î£ a universe-polymorphic type

open import Agda.Primitive using (Level; lzero; lsuc; _â_)
                           renaming (Set to ð¤)
                           public

variable i j k : Level

record Î£ {A : ð¤ i} (B : A â ð¤ j) : ð¤ (i â j) where
 constructor
  _,_
 field
  prâ : A
  prâ : B prâ

open Î£ public
infixr 1 _,_

Sigma : (A : ð¤ i) (B : A â ð¤ j) â ð¤ (i â j)
Sigma {i} {j} A B = Î£ {i} {j} {A} B

syntax Sigma A (Î» x â b) = Î£ x ê A , b

infix -1 Sigma

_Ã_ : ð¤ i â ð¤ j â ð¤ (i â j)
A Ã B = Î£ x ê A , B

-- (x : X) â A x
-- (x : X) Ã A x

infixr 2 _Ã_

-- More general type of negation:

Â¬_ : ð¤ i â ð¤ i
Â¬ A = A â ð

-- Give the identity type more general universe assignments:

data _â¡_ {X : ð¤ i} : X â X â ð¤ i where
 refl : (x : X) â x â¡ x

_â¢_ : {X : ð¤ i} â X â X â ð¤ i
x â¢ y = Â¬ (x â¡ y)

infix 0 _â¡_

â¡-elim : {X : ð¤ i} (A : (x y : X) â x â¡ y â ð¤ j)
       â ((x : X) â A x x (refl x))
       â (x y : X) (p : x â¡ y) â A x y p
â¡-elim A f x x (refl x) = f x

â¡-nondep-elim : {X : ð¤ i} (A : X â X â ð¤ j)
              â ((x : X) â A x x)
              â (x y : X) â x â¡ y â A x y
â¡-nondep-elim A = â¡-elim (Î» x y _ â A x y)

trans : {A : ð¤ i} {x y z : A} â x â¡ y â y â¡ z â x â¡ z
trans p (refl y) = p

sym : {A : ð¤ i} {x y : A} â x â¡ y â y â¡ x
sym (refl x) = refl x

ap : {A : ð¤ i} {B : ð¤ j} (f : A â B) {x y : A} â x â¡ y â f x â¡ f y
ap f (refl x) = refl (f x)

apâ : {A : ð¤ i} {B : ð¤ j} {C : ð¤ k} (f : A â B â C) {x x' : A} {y y' : B}
    â x â¡ x' â y â¡ y' â f x y â¡ f x' y'
apâ f (refl x) (refl y) = refl (f x y)

transport : {X : ð¤ i} (A : X â ð¤ j)
          â {x y : X} â x â¡ y â A x â A y
transport A (refl x) a = a

_â_ : {A : ð¤ i} {x y z : A} â x â¡ y â y â¡ z â x â¡ z
_â_ = trans

infixl 7 _â_

_â»Â¹ : {A : ð¤ i} {x y : A} â x â¡ y â y â¡ x
_â»Â¹ = sym

infix  40 _â»Â¹

_â¤_ : â â â â ð¤
zero â¤ n      = ð
suc a â¤ zero  = ð
suc a â¤ suc b = a â¤ b

-- The (sub)type of prime numbers

â : ð¤â
â = Î£ p ê â , is-prime p

â-inclusion : â â â
â-inclusion = prâ

-- We can prove that this map is left-cancellable, i.e. it satisfies
-- â-inclusion u â¡ â-inclusion u â u â¡ v.
-- Moreover, this map is an embedding (we haven't defined this concept yet).

-- Not quite the type of composite numbers:

CN : ð¤
CN = Î£ x ê â , Î£ (y , z) ê â Ã â , x â¡ y * z

CN' : ð¤
CN' = Î£ x ê â , Î£ (y , z) ê â Ã â , (y â¥ 2) Ã (z â¥ 2) Ã (x â¡ y * z)

CN-projection : CN â â
CN-projection = prâ

-- This map is not left-cancellable, and hence can't be considered to
-- be an an inclusion.

counter-example : CN-projection (6 , (3 , 2) , refl 6)
                â¡ CN-projection (6 , (2 , 3) , refl 6)
counter-example = refl 6

-- But how do we prove that these two tuples are *different*? They
-- certainly do look different. We'll do this later.

-- We will need to define
--
-- CN = Î£ x ê â , â¥ Î£ (y , z) ê â Ã â , x â¡ y * z â¥, or equivalently
-- CN = Î£ x ê â , â (y , z) ê â Ã â , x â¡ y * z â¥
--
-- to really get a *subtype* of composite numbers.


-- Another use of Î£.
-- The type of monoids.

is-prop : ð¤ i â ð¤ i
is-prop X = (x y : X) â x â¡ y

is-set : ð¤ i â ð¤ i
is-set X = (x y : X) â is-prop (x â¡ y)

Mon : ð¤ (lsuc i)
Mon {i} = Î£ X ê ð¤ i  -- data
            , is-set X  -- property (we show that)
            Ã (Î£ ð ê X ,  -- data (but...)
               Î£ _Â·_ ê (X â X â X) -- data
                  , (((x : X) â (x Â· ð â¡ x)) -- (1) property
                  Ã  ((x : X) â (ð Â· x â¡ x)) -- (2) property
                  Ã  ((x y z : X) â (x Â· (y Â· z)) â¡ ((x Â· y) Â· z)))) -- (3) property

-- This can be defined using a record in Agda:

record Mon' : ð¤ (lsuc i) where
 constructor mon
 field
  carrier        : ð¤ i  -- X
  carrier-is-set : is-set carrier
  ð              : carrier
  _Â·_            : carrier â carrier â carrier
  left-unit-law  : (x : carrier) â x Â· ð â¡ x
  right-unit-law : (x : carrier) â ð Â· x â¡ x
  assoc-law      : (x y z : carrier) â x Â· (y Â· z) â¡ (x Â· y) Â· z

Î± : Mon {i} â Mon' {i}
Î± (X , X-is-set , ð , _Â·_ , l , r , a) = mon X X-is-set ð _Â·_ l r a

Î² : Mon' {i} â Mon {i}
Î² (mon X X-is-set ð _Â·_ l r a) = (X , X-is-set , ð , _Â·_ , l , r , a)

Î²Î± : (M : Mon {i}) â Î² (Î± M) â¡ M
Î²Î± = refl

Î±Î² : (M : Mon' {i}) â Î± (Î² M) â¡ M
Î±Î² = refl

-- This kind of proof doesn't belong to the realm of MLTT:

false-is-not-true[not-an-MLTT-proof] : false â¢ true
false-is-not-true[not-an-MLTT-proof] ()

-- Proof in MLTT, which requires a universe (Cf. Ulrik's 2nd HoTT
-- lecture):

_â£_ : Bool â Bool â ð¤â
true  â£ true  = ð
true  â£ false = ð
false â£ true  = ð
false â£ false = ð

â¡-gives-â£ : {x y : Bool} â x â¡ y â x â£ y
â¡-gives-â£ (refl true) = â
â¡-gives-â£ (refl false) = â

false-is-not-true : Â¬ (false â¡ true)
false-is-not-true p = lemma
 where
   lemma : ð
   lemma = â¡-gives-â£ p


false-is-not-true' : Â¬ (false â¡ true)
false-is-not-true' = â¡-gives-â£

-- Notice that this proof is different from the one given by Ulrik in
-- the HoTT track. Exercise: implement Ulrik's proof in Agda.

-- Exercise: prove that Â¬ (0 â¡ 1) in the natural numbers in MLTT style
-- without using `()`.

-- contrapositives.

contrapositive : {A : ð¤ i} {B : ð¤ j} â (A â B) â (Â¬ B â Â¬ A)
contrapositive f g a = g (f a)

Î -Â¬-gives-Â¬-Î£ : {X : ð¤ i} {A : X â ð¤ j}
              â ((x : X) â Â¬ A x)
              â Â¬ (Î£ x ê X , A x)
Î -Â¬-gives-Â¬-Î£ Ï (x , a) = Ï x a

Â¬-Î£-gives-Î -Â¬ : {X : ð¤ i} {A : X â ð¤ j}
              â Â¬ (Î£ x ê X , A x)
              â ((x : X) â Â¬ A x)
Â¬-Î£-gives-Î -Â¬ Î³ x a = Î³ (x , a)


-- Equality in Î£ types.

from-Î£-â¡' : {X : ð¤ i} {A : X â ð¤ j}
            {(x , a) (y , b) : Î£ A}
          â (x , a) â¡ (y , b)
          â Î£ p ê (x â¡ y) , (transport A p a â¡ b)
from-Î£-â¡' (refl (x , a)) = (refl x , refl a)

to-Î£-â¡' : {X : ð¤ i} {A : X â ð¤ j}
          {(x , a) (y , b) : Î£ A}
        â (Î£ p ê (x â¡ y) , (transport A p a â¡ b))
        â (x , a) â¡ (y , b)
to-Î£-â¡' (refl x , refl a) = refl (x , a)

module _ {X : ð¤ i} {A : ð¤ j}
         {(x , a) (y , b) : X Ã A} where

 from-Ã-â¡ : (x , a) â¡ (y , b)
          â (x â¡ y) Ã (a â¡ b)
 from-Ã-â¡ (refl (x , a)) = refl x , refl a


 to-Ã-â¡ : (x â¡ y) Ã (a â¡ b)
        â (x , a) â¡ (y , b)
 to-Ã-â¡ (refl x , refl a) = refl (x , a)

module _ {X : ð¤ i} {A : X â ð¤ j}
         {(x , a) (y , b) : Î£ A} where

 -- x y : X
 -- a : A x
 -- b : A y

 from-Î£-â¡ : (x , a) â¡ (y , b)
          â Î£ p ê (x â¡ y) , transport A p a â¡ b
 from-Î£-â¡ (refl (x , a)) = refl x , refl a


 to-Î£-â¡ : (Î£ p ê (x â¡ y) , (transport A p a â¡ b))
        â (x , a) â¡ (y , b)
 to-Î£-â¡ (refl x , refl a) = refl (x , a)


 contra-from-Î£-â¡ : Â¬ (Î£ p ê (x â¡ y) , (transport A p a â¡ b))
                 â (x , a) â¢ (y , b)
 contra-from-Î£-â¡ = contrapositive from-Î£-â¡

 contra-to-Î£-â¡ : (x , a) â¢ (y , b)
               â Â¬ (Î£ p ê (x â¡ y) , (transport A p a â¡ b))
 contra-to-Î£-â¡ = contrapositive to-Î£-â¡

 to-Î£-â¢ : ((p : x â¡ y) â transport A p a â¢ b)
        â (x , a) â¢ (y , b)
 to-Î£-â¢ u = contra-from-Î£-â¡ (Î -Â¬-gives-Â¬-Î£ u)

 from-Î£-â¢ : (x , a) â¢ (y , b)
          â ((p : x â¡ y) â transport A p a â¢ b)
 from-Î£-â¢ v = Â¬-Î£-gives-Î -Â¬ (contra-to-Î£-â¡ v)
```

We now revisit the example above. How do we prove that aa and bb are
different? It's not easy. We use the above lemmas.

```agda
aa bb : CN
aa = (6 , (3 , 2) , refl 6)
bb = (6 , (2 , 3) , refl 6)
```

To prove that aa â¢ bb, we need to know that â is a set! And this is
difficult. See the module
[Hedbergs-Theorem](../Lecture-Notes/files/Hedbergs-Theorem.lagda.md) for
a complete proof.

For the moment we just assume that â is a set, and prove that 3 â¢ 2 by
cheating (produce a genuine MLTT proof as an exercise).

```agda

3-is-not-2 : 3 â¢ 2
3-is-not-2 ()

example-revisited : is-set â â aa â¢ bb
example-revisited â-is-set = I
 where
  A : â â ð¤â
  A x = Î£ (y , z) ê â Ã â , x â¡ y * z

  II : (p : 6 â¡ 6) â transport A p ((3 , 2) , refl 6) â¢  ((2 , 3) , refl 6)
  II p = VIII
   where
    III : p â¡ refl 6
    III = â-is-set 6 6 p (refl 6)

    IV : transport A p ((3 , 2) , refl 6) â¡ ((3 , 2) , refl 6)
    IV = ap (Î» - â transport A - ((3 , 2) , refl 6)) III

    V : ((3 , 2) , refl 6) â¢ ((2 , 3) , refl 6)
    V q = 3-is-not-2 VII
     where
      VI : (3 , 2) â¡ (2 , 3)
      VI = ap prâ q

      VII : 3 â¡ 2
      VII = ap prâ VI

    VIII : transport A p ((3 , 2) , refl 6) â¢  ((2 , 3) , refl 6)
    VIII r = V IX
     where
      IX : ((3 , 2) , refl 6) â¡ ((2 , 3) , refl 6)
      IX = trans (IV â»Â¹) r

  I : aa â¢ bb
  I = to-Î£-â¢ II
```

If there is time, I will do some isomorphisms.
