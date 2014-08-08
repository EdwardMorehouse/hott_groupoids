{-# OPTIONS --without-K #-}

module Paths where

open import Interlude

{- the equality type -}

infix 4 _==_
-- equality formation
data _==_ {i} {A : Set i}  :  A → A → Set i  where
  -- equality introjuction
  refl  :  (a : A) → a == a

_[_↔_]  :  ∀ {i} → (A : Set i) → A → A → Set i
A [ x ↔ y ]  =  x == y

-- equality elimination
J[_]  :  ∀ {i j} → {A : Set i}
            → (C : {x y : A} → x == y → Set j)   --  motive (target type constructor)
            → ((x : A) → C (refl x))                     --  hyp. s.d. (if the path were refl)
            → {x y : A} → (p : x == y)                --  major premise (some actual path)
            → C p                                               --  result type (motive at major premise)
J[ C ] c (refl x)  =  c x

---------------------------
-- 1-dimensional paths

path-dom  :  ∀ {i} → {A : Set i}
               → {x y : A} → x == y
               → A
path-dom  =  λ {i} {A} {x} {y} p → x

dom  =  path-dom

path-cod  :  ∀ {i} → {A : Set i}
               → {x y : A} → x == y
               → A
path-cod  =  λ {i} {A} {x} {y} p → y

cod  =  path-cod

-- path inverse
path-inv  :  ∀ {i} → {A : Set i}
               → {x y : A} → x == y
               → y == x
path-inv  =  J[ (λ p → cod p == dom p) ] (refl)

!  =  path-inv

-- path composition
path-comp  :  ∀ {i} → {A : Set i} → {x : A}
                  → {y : A} → x == y
                  → {z : A} → y == z
                  → x == z
path-comp  =  J[ (λ p → {z : _} → cod p == z → dom p == z) ]
                          (λ _ → J[ (λ q → dom q == cod q) ] ( refl ))

infixl 5 _∙_
_∙_  =  path-comp

-- path conjugation
path-conjugate  :  ∀ {i} → {A : Set i} → {x y : A}
                         → x == y → x == x → y == y
path-conjugate  =  λ p q → ! p ∙ q ∙ p

conj  =  path-conjugate

{- syntax for composing paths -}

-- common reduct syntax:
path-join-at : ∀ {i} → {A : Set i} → (z : A) → {x y : A} → x == z → y == z → x == y
path-join-at  =  λ z p q → p ∙ ! q

syntax path-join-at z p q  =  p ↘ z ↙ q

{-
-- dan's syntax:
infixr 2 _≡〈_〉_
_≡〈_〉_  :  ∀ {i} → {A : Set i} → (x : A) → {y z : A} → x == y → y == z → x == z
_ ≡〈 p1 〉 p2  =  (p1 ∙ p2)
-}

{- equational reasoning -}

infixr 2  _≡〈_〉_
_≡〈_〉_  :  ∀ {i} → {A : Set i} → (x : A)
                        → {y : A} → x == y
                        → {z : A} → y == z
                        → x == z
_≡〈_〉_  =  λ {i} {A} x {y} p {z} q → path-comp {i} {A} {x} {y} p {z} q

infix 2 _∎
_∎  :  ∀ {i} → {A : Set i} → (x : A) → x == x
_∎  =  refl

path-computation  :  ∀ {i} → {A : Set i} → {x : A} → x == x
path-computation  =  λ {i} {A} {x} → refl x


{- syntax for presheaves -}
_==-  :  ∀ {i} → {A : Set i} → A → A → Set i
_==-  =  λ x y → x == y

-==_  :  ∀ {i} → {A : Set i} → A → A → Set i
-==_  =  λ y x → x == y

-----------------------------
--  properties of 1-paths
-- homework 3.2
{- groupoid laws -}

path-inverse-left  :  ∀ {i} → {A : Set i} → {x y : A} → (p : x == y)
                         → ! p ∙ p == refl y
path-inverse-left  =  J[ (λ p →  ! p ∙ p == (refl ∘ cod) p) ] (refl ⋅ refl)

path-inverse-right  :  ∀ {i} → {A : Set i} → {x y : A} → (p : x == y)
                          → p ∙ ! p == refl x
path-inverse-right  =  J[ (λ p →  p ∙ ! p == (refl ∘ dom) p) ] (refl ⋅ refl)

path-unit-left  :  ∀ {i} → {A : Set i} → {x y : A} → (p : x == y)
                       → refl x ∙ p == p
path-unit-left  =  J[ (λ p → (refl ∘ dom) p ∙ p == p) ] (refl ⋅ refl) 

path-unit-right  :  ∀ {i} → {A : Set i} → {x y : A} → (p : x == y)
                        → p ∙ refl y == p
path-unit-right  =  J[ (λ p → p ∙ (refl ∘ cod) p == p) ] (refl ⋅ refl)

path-assoc  :  ∀ {i} → {A : Set i} → {a : A}
                    → {b : A} → (p : a == b)
                    → {c : A} → (q : b == c)
                    → {d : A} → (r : c == d)
                    → p ∙ (q ∙ r) == (p ∙ q) ∙ r
path-assoc  =  J[ (λ p → {c : _} → (q : cod p == c) → {d : _} → (r : c == d) → p ∙ (q ∙ r) == (p ∙ q) ∙ r) ]
                          (λ _ → J[ (λ q → {d : _} → (r : cod q == d) → refl (dom q) ∙ (q ∙ r) == (refl (dom q) ∙ q) ∙ r) ]
                                         (λ _ → J[ (λ r → refl (dom r) ∙ (refl (dom r) ∙ r) == (refl (dom r) ∙ refl (dom r)) ∙ r) ]
                                                        (refl ⋅ refl)))

{- convenience lemmas -}

-- path inverse is an involution
path-inv-invol  :  ∀ {i} → {A : Set i} {x y : A} (p : x == y)
                      → (! ∘ !) p == p
path-inv-invol  =  J[ (λ p → (! ∘ !) p == p) ] (refl ⋅ refl)

-- inverse of a composition
path-compose-inverse  :  ∀ {i} → {A : Set i} {x : A}
                                 → {y : A} → (p : x == y)
                                 → {z : A} → (q : y == z)
                                 → ! (p ∙ q)  ==  ! q ∙ ! p
path-compose-inverse  =  J[ (λ p → {z : _} → (q : cod p == z) → ! (p ∙ q)  ==  ! q ∙ ! p) ]
                                        (λ y → J[ (λ q → ! ((refl ∘ dom) q ∙ q) == ! q ∙ (! ∘ refl ∘ dom) q ) ]
                                                       (refl ⋅ refl))

--------------------------------------------------

-- paths in function space
infixl 9 _⋅⋅_
_⋅⋅_  :  ∀ {i} → {A B C : Set i}
             → {f1 f2 : A → B} → (p : f1 == f2)
             → {g1 g2 : B → C} → (q : g1 == g2)
             → f1 ⋅ g1 == f2 ⋅ g2
_⋅⋅_  =  λ {i} {A} {B} {C} → J[ (λ p → {g1 g2 : B → C} → g1 == g2 → dom p ⋅ g1 == cod p ⋅ g2) ] 
                                                  (λ f → J[ (λ q → f ⋅ dom q == f ⋅ cod q) ]
                                                                 (λ g → refl (f ⋅ g)))


