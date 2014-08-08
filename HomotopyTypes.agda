{-# OPTIONS --without-K #-}

module HomotopyTypes where

open import Interlude
open import Paths
open import Paths2D
open import PathActions
open import Equivalences

---------------

 -- Truncation level
is-contr  :  ∀ {i} → Set i → Set i
is-contr  =  λ A → Σ A (λ y → (x : A) → x == y)

-- convenience
contr-center  :  ∀ {i} → {A : Set i} → (is-contr A) → A
contr-center  =  fst

contr-path  :  ∀ {i} → {A : Set i} → (H : is-contr A) → (x : A) → x == contr-center H
contr-path  =  snd

is-prop  :  ∀ {i} → Set i → Set i
is-prop  =  λ A → (x y : A) → x == y

is-set  :  ∀ {i} → Set i → Set i
is-set  =  λ A → (x y : A) → is-prop (x == y)

data tlevel  :  Set  where
    -2  :  tlevel
    succ  :  tlevel → tlevel

-1  :  tlevel
-1  =  succ -2

is-type  :  tlevel → ∀ {i} → Set i → Set i
is-type -2  =  is-contr
is-type (succ n)  =  λ A → (x y : A) → is-type n (x == y)


{- every prop is a set (⋆⋆) -}
prop-then-set  :  ∀ {i} → {A : Set i}
                        → is-prop A → is-set A
prop-then-set  =  λ H x y p q →
                        let
                          f  :  (z : _) → x == z
                          f  =  H x
                        in
                                ( p )
                           ≡〈 ! (path-unit-left p) 〉
                                ( refl x ∙ p )
                           ≡〈 ! (path-inverse-left (f x)) ∙∙ refl p 〉
                                ( ! (f x) ∙ f x ∙ p )
                           ≡〈 ! (path-assoc (! (f x)) (f x) p) 〉
                                ( ! (f x) ∙ (f x ∙ p) )
                           ≡〈 refl (! (f x)) ∙∙ ! (tr-path-right p (f x)) 〉
                                ( ! (f x) ∙ (tr (x ==-) p (f x) ) )
                           ≡〈 refl (! (f x)) ∙∙ apd (x ==-) f p 〉            -- this is the crucial step: we can pre-wisker the apd cell with ! (f x)
                                ( ! (f x) ∙ f y )                                              -- the "center": common form of p and q
                           ≡〈 refl (! (f x)) ∙∙ ! (apd (x ==-) f q) 〉
                                ( ! (f x) ∙ (tr (x ==-) q (f x) ) )
                           ≡〈 refl (! (f x)) ∙∙ tr-path-right q (f x) 〉
                                ( ! (f x) ∙ (f x ∙ q) )
                           ≡〈 path-assoc (! (f x)) (f x) q 〉
                                ( ! (f x) ∙ f x ∙ q )
                           ≡〈 path-inverse-left (f x) ∙∙ refl q 〉
                                ( refl x ∙ q )
                           ≡〈 path-unit-left q 〉
                                ( q )  ∎

-- task 1
prop-level  :  ∀ {i} → {A : Set i}
                → is-prop A → is-type -1 A
prop-level  =  λ H x y → let  center  =  H x y  in
                         center , (λ p → prop-then-set H x y p center)

-- task 2
contr-then-prop  :  ∀ {i} → {A : Set i}
                        → is-contr A → is-prop A
contr-then-prop  =  λ H x y →
                                    let
                                      center  =  fst H
                                      path-to-center  =  snd H
                                    in
                                      path-to-center x ∙ ! (path-to-center y)


-- task 3
raise-level'  :  ∀ {i} → (n : tlevel) → (A : Set i) → is-type n A → is-type (succ n) A
raise-level' -2  =  λ A → contr-then-prop ⋅ prop-level
raise-level' (succ n)  =  λ A H x y p q → IH (x == y) (H x y) p q
  where
    IH  =  raise-level' n
{-
raise-level' (succ n)  with  (raise-level' n)
... | IH  =  λ A H x y p q → IH (x == y) (H x y) p q
 -}

-- book theorem-7.1.7
-- slicker:
raise-level  : {n : tlevel} →  ∀ {i} → {A : Set i}
                → is-type n A → is-type (succ n) A
raise-level { -2 }  =  contr-then-prop ⋅ prop-level
raise-level {succ n}  =  λ H x y → IH (H x y)
  where
    IH  =  raise-level {n}
{-
raise-level {succ n}  with  (raise-level {n})
... | IH  =  λ H x y → IH (H x y)
 -}
-- task 4
prop-has-level-succ  :  (n : tlevel) → ∀ {i} → {A : Set i}
                     → is-prop A → is-type (succ n) A
prop-has-level-succ -2  =  prop-level
prop-has-level-succ (succ n)  =  IH ⋅ raise-level {succ n}
  where
    IH  =  prop-has-level-succ n
{-
prop-has-level-succ (succ n)  with  prop-has-level-succ n
... | IH  =  IH ⋅ raise-level {succ n}
 -}
------------------------

postulate
  is-equiv-is-prop : ∀ {i} → {A B : Set i} → (f : A → B) → is-prop (is-biequiv f)

-- book theorem-7.1.9
  product-level  :  {n : tlevel}
                      → ∀ {i} → {A : Set i}
                      → ∀ {j} → {B : A → Set j} 
                      → ((x : A) → is-type n (B x))
                      → is-type n ((x : A) → B x)

-- book theorem-7.1.8
  sigma-level :  {n : tlevel}
                    → ∀ {i} → {A : Set i} → (is-type n A)
                    → ∀ {j} → {B : A → Set j} → ((x : A) → is-type n (B x))
                    → is-type n (Σ A B)

  subtype-path : ∀ {i j} → {A : Set i} → {B : A → Set j}
                    → (β : (x : A) → is-prop (B x))
                    → (m n : Σ A B)
                    → fst m == fst n → m == n

  subtype-path-equiv : ∀ {i j} → {A : Set i} → {B : A → Set j}
                    → (β : (x : A) → is-prop (B x))
                    → (m n : Σ A B)
                    → (fst m == fst n) ≃ (m == n)

----------------

-- task 5
contr-equiv  :  ∀ {i} → {A B : Set i}
                  → is-contr A → is-contr B
                  → A ≃ B
contr-equiv  =  λ HA HB → const (contr-center HB) , mk-biequiv
                                           (const (contr-center HA) , (λ x → ! (contr-path HA x)))
                                           (const (contr-center HA) , (λ y → ! (contr-path HB y)))

-- task 6
equiv-is-contr  :   ∀ {i} → {A B : Set i}
                    → is-contr A → is-contr B
                    → is-contr (A ≃ B)
equiv-is-contr  =  λ HA HB → {!!}

-- task 7
subtype-level  :  {n : tlevel}
                     → ∀ {i} → {A : Set i} → is-type (succ n) A
                     → ∀ {j} → {B : A → Set j} → ((x : A) → is-prop (B x))
                     → is-type (succ n) (Σ A (λ x → B x))
subtype-level {n}  =  λ HA HB → sigma-level {succ n} HA (λ x → raise-prop-to-succ-of-level n (HB x))
  where
    raise-prop-to-succ-of-level  :  (n : tlevel) → ∀ {i} → {A : Set i} → is-prop A → is-type (succ n) A
    raise-prop-to-succ-of-level -2 = prop-level
    raise-prop-to-succ-of-level (succ n)  =  IH ⋅ raise-level {succ n}
      where
        IH  =  raise-prop-to-succ-of-level n
{-
    raise-prop-to-succ-of-level (succ n) with raise-prop-to-succ-of-level n
    ... | IH  =  IH ⋅ raise-level {succ n}
 -}

-- task 8
func-level  :  {n : tlevel} → ∀ {i} → {A B : Set i}
                → is-type n B → is-type n (A → B)
func-level   =  λ {n} HB → product-level {n} (const HB)

equiv-level  :  {n : tlevel} → ∀ {i} → {A B : Set i}
                  → is-type n A → is-type n B → is-type n (A ≃ B)
equiv-level { -2 }  =  equiv-is-contr
equiv-level {succ n} = λ HA HB → subtype-level {n} (func-level {succ n} HB) is-equiv-is-prop

--------------

postulate
  is-type-is-prop  :  {n : tlevel} → ∀ {i} → {A : Set i} → is-prop (is-type n A)

-- task 9
equiv-preserves-level  :  {n : tlevel} → ∀ {i} → {A B : Set i} → A ≃ B → is-type n A → is-type n B
equiv-preserves-level  =  λ Hequiv → {!!}



