{-# OPTIONS --without-K #-}

module Univalence where

open import Interlude
open import Paths
open import PathActions
open import Equivalences

---------------
-- univalence

{- univalence axiom -}
postulate univalence  :  ∀ {i} → {A B : Set i} → is-biequiv (path-to-equiv {i} {A} {B})

ua  :  ∀ {i} → {A B : Set i}
     → A ≃ B → A == B
ua  =  (fst ∘ is-biequiv.retraction) univalence

postulate
  ua-equiv  :  ∀ {i} → {A B : Set i}
     → (A ≃ B) ≃ (A == B)

-- can't figure out how to prove this
-- see Dan's "type≃β"
postulate path-reduce  :   ∀ {i} → {A B : Set i} → (e : A ≃ B) → (coe ∘ ua) e == equiv-map e
-- path-reduce  =  λ e →  {!!}
