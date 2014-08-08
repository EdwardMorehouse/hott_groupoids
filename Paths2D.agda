{-# OPTIONS --without-K #-}

module Paths2D where

open import Interlude
open import Paths

----------------------------
--  2-dimensional paths

-- identity 2path
2refl  :  ∀ {i} → {A : Set i} → (x : A) → refl x == refl x
2refl  =  refl ⋅ refl

-- 2path domains and codomains
2path-dom  :  ∀ {i} → {A : Set i} → {x y : A} → {p q : x == y} → p == q → A
2path-dom  =  λ {i} {A} {x} {y} {p} {q} α → x

2dom  =  2path-dom

2path-cod  :  ∀ {i} → {A : Set i} → {x y : A} → {p q : x == y} → p == q → A
2path-cod  =  λ {i} {A} {x} {y} {p} {q} α → y

2cod  =  2path-cod

-- 2path inverse
2path-inv  :  ∀ {i} → {A : Set i} → {x y : A} → {p q : x == y}
              → p == q → ! p == ! q
2path-inv  =  J[ (λ α → ! (dom α)  == ! (cod α)) ] (! ⋅ refl)

!!  =  2path-inv

-- 2path composition
2path-comp  :  ∀ {i} → {A : Set i} → {x : A}
                  → {y : A} → {p1 p2 : x == y} → p1 == p2
                  → {z : A} → {q1 q2 : y == z} → q1 == q2
                  → p1 ∙ q1 == p2 ∙ q2
2path-comp  =  J[ (λ α → {z : _} → {q1 q2 : 2cod α == z} → (q1 == q2) → dom α ∙ q1 == cod α ∙ q2) ]
                            (λ p → J[ (λ β → p ∙ dom β == p ∙ cod β) ]
                                           (λ q → refl (p ∙ q)) )

infixl 5 _∙∙_
_∙∙_  =  2path-comp

-- 2-path conjugation
path-2conjugate  :  ∀ {i} → {A : Set i}
                          → {x y : A} → {p1 p2 : x == y} → (α : p1 == p2)
                          → {q1 q2 : x == x} → (β : q1 == q2)
                          → ! p1 ∙ q1 ∙ p1 == ! p2 ∙ q2 ∙ p2
path-2conjugate  =  λ α β → !! α ∙∙ β ∙∙ α

2conj  =  path-2conjugate


-----------------------------
--  properties of 2-paths

{- groupoid laws -}

2path-inverse-left  :  ∀ {i} → {A : Set i} → {x y : A} → {p q : x == y} → (α : p == q)
                         → !! α ∙∙ α == path-inverse-left p ∙ 2refl y ∙ ! (path-inverse-left q)
2path-inverse-left  =  J[ (λ α → !! α ∙∙ α == (path-inverse-left ∘ dom) α ∙ (2refl ∘ 2cod) α ∙ (! ∘ path-inverse-left ∘ cod) α ) ]
                                    ( λ p →
                                           ( (!! ∘ refl) p ∙∙ refl p )
                                        ≡〈 path-computation 〉
                                           ( refl (! p ∙ p) )
                                        ≡〈 (! ∘ path-inverse-right) (path-inverse-left p) 〉
                                           ( path-inverse-left p ∙ ! (path-inverse-left p) )
                                        ≡〈 (! ∘ path-unit-right) (path-inverse-left p) ∙∙ (refl ∘ !) (path-inverse-left p) 〉
                                           ( path-inverse-left p ∙ (2refl ∘ cod) p ∙ ! (path-inverse-left p) ∎ )
                                    )

2path-inverse-right  :  ∀ {i} → {A : Set i} → {x y : A} → {p q : x == y} → (α : p == q)
                         → α ∙∙ !! α == path-inverse-right p ∙ 2refl x ∙ ! (path-inverse-right q)
2path-inverse-right  =  J[ (λ α → α ∙∙ !! α == (path-inverse-right ∘ dom) α ∙ (2refl ∘ 2dom) α ∙ (! ∘ path-inverse-right ∘ cod) α ) ]
                                    ( λ p →
                                           ( refl p ∙∙ (!! ∘ refl) p )
                                        ≡〈 path-computation 〉
                                           ( refl (p ∙ ! p) )
                                        ≡〈 (! ∘ path-inverse-right) (path-inverse-right p) 〉
                                           ( path-inverse-right p ∙ ! (path-inverse-right p) )
                                        ≡〈 (! ∘ path-unit-right) (path-inverse-right p) ∙∙ (refl ∘ !) (path-inverse-right p) 〉
                                           ( path-inverse-right p ∙ (2refl ∘ dom) p ∙ ! (path-inverse-right p) ∎ )
                                    )

2path-unit-left  :  ∀ {i} → {A : Set i} → {x y : A} → {p q : x == y} → (α : p == q)
                       → 2refl x ∙∙ α == path-unit-left p ∙ α ∙ ! (path-unit-left q)
2path-unit-left  =  J[ (λ α → (2refl ∘ 2dom) α ∙∙ α == (path-unit-left ∘ dom) α ∙ α ∙ (! ∘ path-unit-left ∘ cod) α) ]
                                (λ p →
                                      ( (2refl ∘ dom) p ∙∙ refl p )
                                   ≡〈 path-computation 〉
                                      ( refl ((refl ∘ dom) p ∙ p) )
                                   ≡〈 (! ∘ path-inverse-right) (path-unit-left p) 〉
                                      ( path-unit-left p ∙ ! (path-unit-left p) )
                                   ≡〈   (! ∘ path-unit-right) (path-unit-left p) ∙∙ (refl ∘ !) (path-unit-left p)   〉
                                      ( path-unit-left p ∙ refl p ∙ ! (path-unit-left p) ∎ )
                              )

2path-unit-right  :  ∀ {i} → {A : Set i} → {x y : A} → {p q : x == y} → (α : p == q)
                       → α ∙∙ 2refl y == path-unit-right p ∙ α ∙ ! (path-unit-right q)
2path-unit-right  =   J[ (λ α → α ∙∙ (2refl ∘ 2cod) α == (path-unit-right ∘ dom) α ∙ α ∙ (! ∘ path-unit-right ∘ cod) α) ]
                                 (λ p →
                                      ( refl p ∙∙ (2refl ∘ cod) p )
                                   ≡〈 path-computation 〉
                                      ( refl (p ∙ (refl ∘ cod) p) )
                                   ≡〈 (! ∘ path-inverse-right) (path-unit-right p) 〉
                                      ( path-unit-right p ∙ ! (path-unit-right p) )
                                   ≡〈   (! ∘ path-unit-right) (path-unit-right p) ∙∙ (refl ∘ !) (path-unit-right p)   〉
                                      ( path-unit-right p ∙ refl p ∙ ! (path-unit-right p) ∎ )
                              )

2path-assoc  :  ∀ {i} → {A : Set i} → {w : A}
                      → {x : A} → {p1 p2 : w == x} → (α : p1 == p2)
                      → {y : A} → {q1 q2 : x == y} → (β : q1 == q2)
                      → {z : A} → {r1 r2 : y == z} → (γ : r1 == r2)
                      → α ∙∙ (β ∙∙ γ) == path-assoc p1 q1 r1 ∙ ((α ∙∙ β) ∙∙ γ) ∙ ! (path-assoc p2 q2 r2)
2path-assoc  =  J[ (λ α → {y : _} → {q1 q2 : 2cod α == y} → (β : q1 == q2) → {z : _} → {r1 r2 : y == z} → (γ : r1 == r2)
                             → α ∙∙ (β ∙∙ γ) == path-assoc (dom α) q1 r1 ∙ ((α ∙∙ β) ∙∙ γ) ∙ ! (path-assoc (cod α) q2 r2))
                         ] (λ p → J[ (λ β → {z : _} → {r1 r2 : 2cod β == z} → (γ : r1 == r2)
                                            → (refl p) ∙∙ (β ∙∙ γ) == path-assoc p (dom β) r1 ∙ ((refl p ∙∙ β) ∙∙ γ) ∙ ! (path-assoc p (cod β) r2))
                                         ] (λ q → J[ (λ γ
                                                            → refl p ∙∙ (refl q ∙∙ γ) == path-assoc p q (dom γ) ∙ ((refl p ∙∙ refl q) ∙∙ γ) ∙ ! (path-assoc p q (cod γ)))
                                                         ] (λ r → 
                                                                   ( refl p ∙∙ (refl q ∙∙ refl r ) )
                                                                ≡〈 path-computation 〉
                                                                   ( refl (p ∙ (q ∙ r)) )
                                                                ≡〈  (! ∘ path-inverse-right) (path-assoc p q r)   〉
                                                                   ( path-assoc p q r ∙ ! (path-assoc p q r) )
                                                                ≡〈 (! ∘ path-unit-right) (path-assoc p q r) ∙∙ refl (! (path-assoc p q r)) 〉
                                                                   ( path-assoc p q r ∙ ((refl p ∙∙ refl q) ∙∙ refl r) ∙ ! (path-assoc p q r) ∎ )
                                                              )))


{- convenience lemmas -}

2path-inv-invol  :  ∀ {i} → {A : Set i} → {x y : A} → {p q : x == y} → (α : p == q)
                      → (!! ∘ !!) α == path-inv-invol p ∙ α ∙ ! (path-inv-invol q)
2path-inv-invol  =  J[ (λ α → (!! ∘ !!) α == (path-inv-invol ∘ dom) α  ∙ α ∙ ! ((path-inv-invol ∘ cod) α)) ]
                                 (λ p → 
                                        ( (!! ∘ !! ∘ refl) p )
                                     ≡〈 path-computation 〉
                                        ( (refl ∘ ! ∘ !) p )
                                     ≡〈 (! ∘ path-inverse-right) (path-inv-invol p) 〉
                                        ( path-inv-invol p ∙ ! (path-inv-invol p) )
                                     ≡〈 (! ∘ path-unit-right) (path-inv-invol p) ∙∙ (refl ∘ !) (path-inv-invol p) 〉
                                        ( path-inv-invol p ∙ refl p ∙ ! (path-inv-invol p) ∎ )
                                 )

-- 2inverse of a 2composition
2path-compose-inverse  :  ∀ {i} → {A : Set i} → {x : A}
                                 → {y : A} → {p1 p2 : x == y} → (α : p1 == p2)
                                 → {z : A} → {q1 q2 : y == z} → (β : q1 == q2)
                                 → !! (α ∙∙ β)  ==  (path-compose-inverse p1 q1) ∙ (!! β ∙∙ !! α) ∙ ! (path-compose-inverse p2 q2)
2path-compose-inverse  =  J[ (λ α → {z : _} → {q1 q2 : (2cod α) == z} → (β : q1 == q2)
                                              → !! (α ∙∙ β) == (path-compose-inverse (dom α) q1) ∙ (!! β ∙∙ !! α) ∙ ! (path-compose-inverse (cod α) q2))
                                         ] (λ p → J[ (λ β
                                                           → !! ((refl p) ∙∙ β) == path-compose-inverse p (dom β) ∙ (!! β ∙∙ !! (refl p)) ∙ ! (path-compose-inverse p (cod β)))
                                                        ] (λ q →
                                                             ( !! ((refl p) ∙∙ (refl q)) )
                                                             ≡〈 path-computation 〉
                                                             ( refl (! (p ∙ q)) )
                                                             ≡〈 (! ∘ path-inverse-right) (path-compose-inverse p q) 〉
                                                             ( path-compose-inverse p q ∙ ! (path-compose-inverse p q) )
                                                             ≡〈 (! ∘ path-unit-right) (path-compose-inverse p q) ∙∙ (refl ∘ !) (path-compose-inverse p q) 〉
                                                             ( (path-compose-inverse p q) ∙ (!! (refl q) ∙∙ !! (refl p)) ∙ ! (path-compose-inverse p q) ∎ )
                                                          ))


-- interchange
interchange  :  ∀ {i} → {A : Set i} → {x : A}
                                  → {y : A} → {p : x == y}
                                  → {q : x == y} → (α : p == q)
                                  → {r : x == y} → (β : q == r)
                                  → {z : A} → {s : y == z}
                                  → {t : y == z} → (γ : s == t)
                                  → {u : y == z} → (δ : t == u)
                                  → (α ∙∙ γ) ∙ (β ∙∙ δ) == (α ∙ β) ∙∙ (γ ∙ δ)
interchange  =  J[ (λ α → {r : 2dom α == 2cod α} → (β : cod α == r) → {z : _} → {s t : 2cod α == z}→ (γ : s == t) → {u : 2cod α == z} → (δ : t == u)
                               → (α ∙∙ γ) ∙ (β ∙∙ δ) == (α ∙ β) ∙∙ (γ ∙ δ))
                         ] (λ _ → J[ (λ β → {z : _} → {s t : 2cod β == z} → (γ : s == t) → {u : 2cod β == z} → (δ : t == u)
                                          → ((refl ∘ dom) β ∙∙ γ) ∙ (β ∙∙ δ) == ((refl ∘ dom) β ∙ β) ∙∙ (γ ∙ δ))
                                        ] (λ q → J[ (λ γ → {u : 2dom γ == 2cod γ} → (δ : cod γ == u)
                                                          → (refl q ∙∙ γ) ∙ (refl q ∙∙ δ) == (refl q ∙ refl q) ∙∙ (γ ∙ δ))
                                                       ] (λ _ → J[ (λ δ → (refl q ∙∙ (refl ∘ dom) δ) ∙ (refl q ∙∙ δ) == (refl q ∙ refl q) ∙∙ ((refl ∘ dom) δ ∙ δ))
                                                                     ] (λ t →
                                                                          ( (refl q ∙∙ refl t) ∙ ((refl q ∙∙ refl t)) )
                                                                       ≡〈 path-computation 〉
                                                                          ( refl (q ∙ t) )
                                                                       ≡〈 path-computation 〉
                                                                          ( (refl q ∙ refl q) ∙∙ (refl t ∙ refl t) ∎ )
                                                                       ))))