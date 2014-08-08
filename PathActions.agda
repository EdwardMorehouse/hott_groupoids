{-# OPTIONS --without-K #-}

module PathActions where

open import Interlude
open import Paths
open import Paths2D

{- ap -}

--  action of a non-dependent map on a 1-path:
ap  :  ∀ {i} → {A B : Set i} → (f : A → B) → {a1 a2 : A}
            → a1 == a2 → f a1 == f a2
ap  =  λ f → J[ (λ p → (f ∘ dom) p == (f ∘ cod) p) ] (f ⋅ refl)

--  action of a non-dependent map on a 2-path:
ap2  :  ∀ {i} → {A B : Set i} → (f : A → B) → {a1 a2 : A} → {p1 p2 : a1 == a2}
             → p1 == p2 → ap f p1 == ap f p2
ap2  =  λ f → J[ (λ α → (ap f ∘ dom) α == (ap f ∘ cod) α) ] (ap f ⋅ refl)

-- is it possible to give a type for ap n?
-- i suppose first i need to type path n


{- ap f preserves groupoid structure -}

ap-refl  :  ∀ {i} → {A B : Set i} → (f : A → B) → {x : A}
               → ap f (refl x) == refl (f x)
ap-refl  =  λ f → λ {x} → (refl ∘ refl ∘ f) x

ap-inv  :  ∀ {i} → {A B : Set i} → (f : A → B)
               → {x y : A} → (p : x == y)
               → ap f (! p) == ! (ap f p)
ap-inv  =  λ f → J[ (λ p → ap f (! p) == ! (ap f p)) ]
                             (f ⋅ refl ⋅ refl)

-- homework 4.1.1 (unbiased)
ap-comp  :  ∀ {i} → {A B : Set i} → (f : A → B)
                   → {x y : A} → (p : x == y)
                   → {z : A} → (q : y == z)
                   → (ap f (p ∙ q)) == (ap f p ∙ ap f q)
ap-comp  =  λ f → J[ (λ p → {z : _} → (q : cod p == z) → ap f (p ∙ q) == (ap f p) ∙ (ap f q)) ]
                                (λ _ → J[ (λ q → ap f ((refl ∘ dom) q ∙ q) == (ap f ((refl ∘ dom) q)) ∙ ap f q) ]
                                               ( f ⋅ refl ⋅ refl))
{-
ap-comp  =  λ f → J[ (λ p → {z : _} → (q : cod p == z) → ap f (p ∙ q) == (ap f p) ∙ (ap f q)) ]
                   (λ y q → ap2 f (path-unit-left q) ↘ ap f q ↙ (ap-refl f ∙∙ refl (ap f q)) ∙ path-unit-left _)  -- left-biased
-}

{- ap along an identity function -}
id-ap  :  ∀ {i} → {A : Set i} → {x y : A} → (p : x == y)
          → ap id[ A ] p == p
id-ap  =  J[ (λ p → ap id p == p) ] (refl ⋅ refl)

-- homework 4.1.2
{- ap along a composition of functions -}
comp-ap  :  ∀ {i} → {A B C : Set i} → (f : A → B) → (g : B → C)
                   → {x y : A} → (p : x == y)
                   → ap (g ∘ f) (p) == (ap g ∘ ap f) (p)
comp-ap  =  λ f g → J[ (λ p → ap (g ∘ f) p == (ap g ∘ ap f) p) ] (f ⋅ g ⋅ refl ⋅ refl)


{- transportation in a dependent type -}

-- transport of a point along a path
tr  :  ∀ {i j} → {A : Set i} → (B : A → Set j)
     → {a1 a2 : A} → a1 == a2
     → B (a1) → B (a2)
tr  =  λ B → J[ (λ p → (B ∘ dom) p → (B ∘ cod) p) ] (λ a → id[ B (a) ])

-- transport of a path along a path
tr-path  :  ∀ {i j} → {A : Set i} → (B : A → Set j)
            → {a1 a2 : A} → (p : a1 == a2)
            → {x y : B a1} → x == y
            → tr B p x == tr B p y
tr-path  =  λ B → J[ (λ p → {x y : (B ∘ dom) p} → x == y → tr B p x == tr B p y) ] (λ a {x} {y} → id[ x == y ])  -- by induction on p
--tr-path  =  λ B p → J[ (λ q → tr B p (dom q) == tr B p (cod q)) ] (tr B p ⋅ refl)  -- by induction on q


-- transport of a point along a 2-path
2-tr  :  ∀ {i j} → {A : Set i} → (B : A → Set j)
              → {a1 a2 : A} → {p1 p2 : a1 == a2} → p1 == p2
              → (x : B a1)
              → tr B p1 x == tr B p2 x
2-tr  =  λ B → J[ (λ α → (x : (B ∘ 2dom) α) → tr B (dom α) x == tr B (cod α) x) ] (λ p → tr B p ⋅ refl)

{- transport of a path along a 2-path -}
2-tr-path  :  ∀ {i j} → {A : Set i} → (B : A → Set j)
              → {a1 a2 : A} → {p1 p2 : a1 == a2} → p1 == p2
              → {x y : B a1} → x == y
              → tr B p1 x == tr B p2 y
2-tr-path  =  λ B → J[ (λ α → {x y : (B ∘ 2dom) α} → x == y → tr B (dom α) x == tr B (cod α) y) ] (λ p q → tr-path B p q)


{- transport respects groupoid structure -}

tr-refl  :  ∀ {i j} → {A : Set i} → {B : A → Set j} → (a : A) → (x : B a)
                 → tr B (refl a) x == id x
tr-refl  =  λ a x → refl x


tr-cat  :  ∀ {i j} → {A : Set i} → {B : A → Set j} → {a1 a2 a3 : A} → (p : a1 == a2) → (q : a2 == a3) → (x : B a1)
                → (tr B p ⋅ tr B q) (x) == tr B (p ∙ q) (x)
tr-cat  =  λ {i} {j} {A} {B} {a1} {a2} {a3} p q x → J[ (λ {a1'} {a2'} p' → (q' : a2' == a3) → (x' : B a1') →  (tr B p' ⋅ tr B q') (x') == tr B (p' ∙ q') (x')) ]
                                      (λ a q' x' → ((ap (tr B q') (tr-refl {B = B} a x'))) ↘ (tr B q' x') ↙ (2-tr B (path-unit-left q') x')) p q x
 

tr-path-refl  :  {A : Set} → {B : A → Set} → (a : A) → {x y : B a} → (p : x == y)
                  → tr-path B (refl a) p == id p
tr-path-refl  =  λ a p → refl p  -- for tr-path by J(p)
--tr-path-refl  =  λ {A} {B} a → J[ (λ p → tr-path B (refl a) p == p) ] (refl ⋅ refl)  -- for tr-path by J(q)



{- function extensionality -}

happly  :  ∀ {i} → {A : Set i} → {B : A → Set i} → {f g : Π A B}
            → (f == g) → ((x : A) → f x == g x)
happly p x = ap (λ u → u x) p

-- function extensionality axiom
postulate funext  :  ∀ {i j} → {A : Set i} → {B : A → Set j} → {f g : Π A B}
                          → ((x : A) → f x == g x) → f == g

postulate funext'  :  ∀ {i j} → {A : Set i} → {B : A → Set j} → {f g : Π A B}
                          → ({x : A} → f x == g x) → f == g


-- book lemma 2.11.2
-- lecture 13-??:??:??  TODO
{- transport in an identity fibration is path composition (lecture 2013.10.28) -}
{- this is just the covariant yoneda functor ℂ(z → -) : ℂ → Set -}
tr-path-right  :  ∀ {i} → {A : Set i} → {x : A}
                  → {y : A} → (p : x == y)
                  → {z : A} → (q : z == x)
                  → tr (z ==-) p q == q ∙ p
tr-path-right  =  J[ (λ p → {z : _} → (q : z == dom p) → tr (z ==-) p q == q ∙ p) ]
                            (λ x q →
                                    ( tr (dom q ==-) (refl x) q )
                                ≡〈 path-computation 〉
                                    ( q )
                                ≡〈 ! (path-unit-right q) 〉
                                    ( q ∙ refl x ) ∎
                            )

{- this is just the contravariant yoneda functor ℂ(- → z) : ℂ° → Set -}
tr-path-left  :  ∀ {i} → {A : Set i} → {x : A}
                  → {y : A} → (p : x == y)
                  → {z : A} → (q : x == z)
                  → tr (-== z) p q == ! p ∙ q
tr-path-left  =  J[ (λ p → {z : _} → (q : dom p == z) → tr (-== z) p q == ! p ∙ q) ]
                            (λ x q →
                                    ( tr (-== cod q) (refl x) q )
                                ≡〈 path-computation 〉
                                    ( q )
                                ≡〈 ! (path-unit-left q) 〉
                                    ( ! (refl x) ∙ q ) ∎
                            )

tr-path-loop  :  ∀ {i} → {A : Set i} → {x : A}
                  → {y : A} → (p : x == y)
                  → (q : x == x)
                  → tr (λ w → w == w) p q == ! p ∙ q ∙ p
tr-path-loop  =  J[ (λ p → (q : dom p == dom p) → tr (λ w → w == w) p q == ! p ∙ q ∙ p) ]
                            (λ x q → 
                                    ( tr (λ w → w == w) (refl x) q )
                                ≡〈 path-computation 〉
                                    ( q )
                                ≡〈 ! (path-unit-left _) ∙ ! (path-unit-right _) 〉
                                    ( ! (refl x) ∙ q ∙ refl x ) ∎
                            )


{-
tr-path-right  :  ∀ {i} → {A : Set i} → (x : A)
        → {y1 y2 : A} → (q : y1 == y2)
        → (tr (λ y → x == y) q) == (λ p → p ∙ q)
tr-path-right  =  λ x → J[ (λ q → (tr (λ y → x == y) q) == (λ p → p ∙ q)) ]
--                       (λ y → (funext (tr-path-refl y) ↘ (λ p → p) ↙ funext path-unit-right))
                                      (λ y → funext (λ p →
                                              ( tr (λ y → x == y) (refl y) p )
                                          ≡〈 path-computation 〉
                                              ( p )
                                          ≡〈 ! (path-unit-right p) 〉
                                              ( p ∙ refl y ) ∎
                                      ))


tr-path-left  :  ∀ {i} → {A : Set i} → (y : A)
        → {x1 x2 : A} → (p : x1 == x2)
        → (tr (λ x → x == y) p) == (λ q → ! p ∙ q)
tr-path-left  =  λ y → J[ (λ p → (tr (λ x → x == y) p) == (λ q → ! p ∙ q)) ]
--                       (λ x → (funext (tr-path-refl x) ↘ (λ q → q) ↙ funext path-unit-left))
                                      (λ x → funext (λ q →
                                              ( tr (λ x → x == y) (refl x) q )
                                          ≡〈 path-computation 〉
                                              ( q )
                                          ≡〈 ! (path-unit-left q) 〉
                                              ( refl x ∙ q ) ∎
                                      ))

tr-path-loop  :  {A : Set}
        → {x1 x2 : A} → (p : x1 == x2)
        → (tr (λ x → x == x) p) == (λ q → ! p ∙ q ∙ p)
tr-path-loop  =  J[ (λ p → (tr (λ x → x == x) p) == (λ q → ! p ∙ q ∙ p)) ]
             (λ x → (funext (tr-path-refl x ) ↘ (λ q → q) ↙ funext (λ p → (path-unit-left p ∙∙ (refl ∘ refl) x) ∙ path-unit-right p)))
-}



{- apd -}
apd  :  ∀ {i j} → {A : Set i} → (B : A → Set j)
        → (f : Π A B)
        → {a1 a2 : A} → (p : a1 == a2)
        → tr B p (f a1) == f (a2)                                    --  why no work (tr p ∘ f) a1 ??
apd  =  λ B f p → J[ (λ {a1'} {a2'} p' → (tr B p') (f a1') == f a2') ] (f ⋅ refl) p


-- coerce a path to a function
coe  :  ∀ {i} → {A B : Set i} → (A == B) → (A → B)
coe  =  tr id




{- homework 3.1.2 -}
trans''  :  ∀ {i} → {A : Set i} → {x : A}
                    → {y : A} → (x == y)
                    → {z : A} → (y == z)
                    → x == z
trans''  =  λ p q → tr (λ a → dom p == a) q p

tr-const  :  ∀ {i j} → {A : Set i} → {B : Set j} → {a1 a2 : A} → (p : a1 == a2) → (b : B)
                           → tr (const B) p b == b
tr-const  =  λ {i} {j} {A} {B} → J[ (λ p → (b : B) → tr (const B) p b == b) ] (tr-refl)

{- homework 3.1.3 -}
ap'  :  ∀ {i j} → {A : Set i} → {B : Set j} → (f : A → B) → {a1 a2 : A}
             → a1 == a2 → f a1 == f a2
ap'  =  λ {i} {j} {A} {B} f p → ! ((tr-const p  ∘ f  ∘ dom) p) ∙ apd (const B) f p


{- ahh, the intended solution: -}
ap''  :  {A B : Set} → (f : A → B) → {a1 a2 : A}
              → a1 == a2 → f a1 == f a2
ap''  =  λ f {a1} p → tr (λ a → a1 == a → f (a1) == f (a)) p (const ((refl ∘ f) a1)) (p)
--ap''  =  λ {A} f {a1} {a2} p → tr (λ a → a1 == a → f (a1) == f (a)) p (const ((refl ∘ f) a1)) p


