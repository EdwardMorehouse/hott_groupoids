{-# OPTIONS --without-K #-}

module Interlude where

-- from the standard library:
open import  Level  public  using (Level ; _⊔_)
open import  Function  public  using (id ; const ; flip ; _∘_ ; case_return_of_ ; case_of_)
open import  Data.Unit  public  using (⊤)  renaming (tt to ⋆)
open import  Data.Empty  public  using (⊥)  renaming (⊥-elim to abort)
open import  Data.Product  public  using (Σ ; _,_ ; _×_ ; curry ; uncurry)  renaming (proj₁ to fst ; proj₂ to snd ; <_,_> to ⟨_,_⟩)
open import  Data.Sum  public  using ([_,_])  renaming (_⊎_ to _+_ ; inj₁ to inl ; inj₂ to inr ; [_,_]′ to [_,_]')
open import  Data.Bool  public  using (Bool ; true ; false ; not ; if_then_else_)  renaming (T to reflectBool)
open import  Data.Nat  public  using (ℕ ; zero)  renaming (suc to succ ; _+_ to _++_ ; _*_ to _××_)
open import  Relation.Nullary  public  using (¬_)


{- convenience -}

-- Π type
Π  :  ∀ {i j} → (A : Set i) → (B : A → Set j) → Set  (i ⊔ j)
Π A B  =  (x : A) → B x

-- Σ and Π syntax
Σ-syntax  :  ∀ {i j} (A : Set i) → (A → Set j) → Set (i ⊔ j)
Σ-syntax  =  Σ

syntax  Σ-syntax A (λ x → B)  =  Σ[ x ∈ A ] B

Π-syntax  :  ∀ {i j} (A : Set i) → (A → Set j) → Set (i ⊔ j)
Π-syntax  =  Π

syntax  Π-syntax A (λ x → B)  =  Π[ x ∈ A ] B


-- dependent function composition (normal order)
infixl 9 _⋅_
_⋅_  :  ∀ {i j k} → {A : Set i} → {B : A → Set j} → {C : (x : A) → B x → Set k}
             → (f : (x : A) → B x)
             → (g : {x : A} → (y : B x) → C x y)
             → (x : A) → C x (f x)
f ⋅ g  =  λ x → g (f x)

-- iteration
iterate  :  ∀ {i} → {A : Set i} → ℕ → (A → A) → A → A
iterate zero f  =  id
iterate (succ n) f  =  f ⋅ iterate n f

_^[_]  :  ∀ {i} → {A : Set i} → (A → A) → ℕ → A → A
_^[_]  =  flip iterate

-- identity function at explicit type (docmentational)
id[_]  :  ∀ {i} (A : Set i) → A → A
id[_]  =  λ t → id {_} {t}

{-
natind  :  ∀ {i} → (A : ℕ → Set i) → (A zero) → ((n : ℕ) → A n → A (succ n)) → (n : ℕ) → A n
natind A z s zero = z
natind A z s (succ n)  with  natind A z s n
... | H = s n H
-}

natind  :  ∀ {i} → (A : ℕ → Set i) → (A zero) → ((n : ℕ) → A n → A (succ n)) → (n : ℕ) → A n
natind A base step zero  =  base
natind A z s (succ n)  =  s n H
  where
    H  =  natind A z s n
