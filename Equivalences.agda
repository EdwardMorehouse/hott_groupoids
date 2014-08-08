{-# OPTIONS --without-K #-}

module Equivalences where

open import Interlude
open import Paths
open import Paths2D
open import PathActions


record is-biequiv {i j} {A : Set i} {B : Set j} (f : A → B)  :  Set (i ⊔ j)  where
  constructor  mk-biequiv
  field
    retraction  :  Σ (B → A) (λ r → (x : A) → r (f x) == x)
    section      :  Σ (B → A) (λ s → (y : B) → f (s y) == y)


infixl 1 _≃_
_≃_  :  ∀ {i j} → (A : Set i) → (B : Set j) → Set (i ⊔ j)
_≃_  =  λ {i j} A B → Σ (A → B) (is-biequiv {i} {j} {A} {B})

-- help for accessing parts of an biequivalence
-- since i'm not sold on the implementation

equiv-map  :  ∀ {i  j} → {A : Set i} → {B : Set j} → A ≃ B → A → B
equiv-map  =  fst

retraction-map  :  ∀ {i  j} → {A : Set i} → {B : Set j} → A ≃ B → B → A
retraction-map  =  snd ⋅ is-biequiv.retraction ⋅ fst

retraction-proof  :  ∀ {i  j} → {A : Set i} → {B : Set j} → (e : A ≃ B) → (x : A) → (retraction-map e ∘ equiv-map e) x == x
retraction-proof  =  snd ⋅ is-biequiv.retraction ⋅ snd

section-map  :  ∀ {i  j} → {A : Set i} → {B : Set j} → A ≃ B → B → A
section-map  =  snd ⋅ is-biequiv.section ⋅ fst

section-proof  :  ∀ {i  j} → {A : Set i} → {B : Set j} → (e : A ≃ B) → (y : B) → (equiv-map e ∘ section-map e) y == y
section-proof  =  snd ⋅ is-biequiv.section ⋅ snd

{- equivalence is an equivalence relation -}

-- homework 4.8
equiv-refl  :  ∀ {i} → {A : Set i} → A ≃ A
equiv-refl  =  id , mk-biequiv (id , refl) (id , refl)

-- homework 4.9
equiv-symm  :  ∀ {i} → {A B : Set i} → A ≃ B → B ≃ A
equiv-symm  =  λ e → section-map e ⋅ equiv-map e ⋅ retraction-map e ,
                           mk-biequiv
                             (equiv-map e , happly
                               (
                                     ( section-map e ⋅ equiv-map e ⋅ retraction-map e ⋅ equiv-map e )
                                 ≡〈 refl (section-map e) ⋅⋅ funext (retraction-proof e) ⋅⋅ refl (equiv-map e) 〉
                                      ( section-map e ⋅ equiv-map e )
                                 ≡〈 funext (section-proof e) 〉
                                      ( id ) ∎
                                )
                             )
                             (equiv-map e , happly
                               (
                                     ( equiv-map e ⋅ section-map e ⋅ equiv-map e ⋅ retraction-map e )
                                 ≡〈 refl (equiv-map e) ⋅⋅ funext (section-proof e) ⋅⋅ refl (retraction-map e) 〉
                                     ( equiv-map e ⋅ retraction-map e )
                                 ≡〈 funext (retraction-proof e) 〉
                                     ( id ) ∎
                               )
                             )

-- homework 4.10
equiv-trans  :  ∀ {i} → {A B C : Set i} → A ≃ B → B ≃ C → A ≃ C
equiv-trans  =  λ e1 e2 → equiv-map e1 ⋅ equiv-map e2 ,
                           mk-biequiv
                              (retraction-map e2 ⋅ retraction-map e1 , happly
                                  (
                                        ( equiv-map e1 ⋅ equiv-map e2 ⋅ retraction-map e2 ⋅ retraction-map e1 )
                                    ≡〈 refl (equiv-map e1) ⋅⋅ funext (retraction-proof e2) ⋅⋅ refl (retraction-map e1) 〉
                                        ( equiv-map e1 ⋅ retraction-map e1 )
                                    ≡〈 funext (retraction-proof e1) 〉
                                        ( id ) ∎
                                  )
                              )
                              (section-map e2 ⋅ section-map e1 , happly
                                  (
                                        ( section-map e2 ⋅ section-map e1 ⋅ equiv-map e1 ⋅ equiv-map e2 )
                                    ≡〈 refl (section-map e2) ⋅⋅ funext (section-proof e1) ⋅⋅ refl (equiv-map e2) 〉
                                        ( section-map e2 ⋅ equiv-map e2 )
                                    ≡〈 funext (section-proof e2) 〉
                                        ( id ) ∎
                                  )
                              )

{- any path between types yields an equivalence -}
path-to-equiv  :  ∀ {i} → {A B : Set i} → A == B → A ≃ B
path-to-equiv  =  J[ (λ p → dom p ≃ cod p) ]
                              (λ _ → equiv-refl)


-- lecture 18-00:54:30
{- quasi-inverse -}
record is-qinv {i j} {A : Set i} {B : Set j} (f : A → B)  :  Set (i ⊔ j)  where
  constructor  mk-qinv
  field
    qinv  :  Σ (B → A) (λ g →
                    (
                      ((x : A) → (g ∘ f) x == x)
                                         ×
                      ((y : B) → (f ∘ g) y == y))
                    )
open is-qinv public

-- book lemma 4.1.1
-- lecture 18-00:56:15
-- lecture 19-00:00:30
postulate qinv-loopspace  :  ∀ {i j} → {A : Set i} → {B : Set j} → (f : A → B)
                             → is-qinv f ≃ ((x : A) → x == x)
-- TODO



