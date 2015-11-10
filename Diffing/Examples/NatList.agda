open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Diff
open import Diffing.Residual
-- open import Diffing.DiffCorrect

module Diffing.Examples.NatList where

  -- Natural numbers,
  nat : {n : ℕ} → U n
  nat = μ (u1 ⊕ vl)

  -- Z : {n : ℕ}{t : Tel n} → ElU nat t
  pattern Z = mu (inl void)

  -- S : {n : ℕ}{t : Tel n} → ElU nat t → ElU nat t
  pattern S n = mu (inr (top n))

  to-nat : {n : ℕ}{t : Tel n} → ℕ → ElU nat t
  to-nat zero = Z
  to-nat (suc x) = S (to-nat x)

  to-ℕ : {n : ℕ}{t : Tel n} → ElU nat t → ℕ
  to-ℕ Z = zero
  to-ℕ (S n) = suc (to-ℕ n)

  to-nat-0 : ℕ → ElU nat tnil
  to-nat-0 = to-nat

  gapplyℕ : D tnil nat → ℕ → Maybe ℕ
  gapplyℕ d n with gapply d (to-nat-0 n)
  ...| nothing = nothing
  ...| just x  = just (to-ℕ x)

  -- Lists,
  list : {n : ℕ} → U (suc n)
  list = μ (u1 ⊕ (wk vl) ⊗ vl)

  -- NIL : {n : ℕ}{t : Tel (suc n)} → ElU list t
  pattern NIL = mu (inl void)

  -- CONS : {n : ℕ}{a : U n}{t : Tel n} 
  --     → ElU a t → ElU list (tcons a t) → ElU list (tcons a t)
  pattern CONS a as = mu (inr ((pop (top a)) , (top as)))

  -- Lists of nats
  nat-list : {n : ℕ} → U n
  nat-list = β list nat

  to-nat-list : List ℕ → ElU nat-list tnil
  to-nat-list [] = red NIL
  to-nat-list (x ∷ xs) with to-nat-list xs
  ...| (red (mu res)) = red (CONS (to-nat x) (mu res))

  from-nat-list : ElU nat-list tnil → List ℕ
  from-nat-list (red NIL) = []
  from-nat-list (red (CONS x xs)) = to-ℕ x ∷ from-nat-list (red xs)

  l1 : ElU nat-list tnil
  l1 = to-nat-list (1 ∷ 2 ∷ [])

  l2 : ElU nat-list tnil
  l2 = to-nat-list (1 ∷ 6 ∷ [])

  l3 : ElU nat-list tnil
  l3 = to-nat-list (2 ∷ 4 ∷ 1 ∷ [])

  d12 : D tnil nat-list
  d12 = gdiff l1 l2

  d13 : D tnil nat-list
  d13 = gdiff l1 l3

  -- booleans
  bool : {n : ℕ} → U n
  bool = u1 ⊕ u1

  pattern TRUE = inl void
  pattern FALSE = inr void

  -- List of Bools
  bool-list2 : {n : ℕ} → U n
  bool-list2 = β list (β list bool)

  b1 : ElU bool-list2 tnil
  b1 = red (CONS (red (CONS TRUE (CONS FALSE NIL))) 
           (CONS (red (CONS FALSE NIL)) 
           NIL))

  b2 : ElU bool-list2 tnil
  b2 = red (CONS (red (CONS TRUE (CONS FALSE NIL))) 
           (CONS (red (CONS FALSE NIL)) 
           (CONS (red NIL) 
           NIL)))

  b2' : ElU bool-list2 tnil
  b2' = red (CONS (red (CONS TRUE NIL)) 
           (CONS (red (CONS FALSE NIL)) 
           (CONS (red NIL) 
           NIL)))

  b3 : ElU bool-list2 tnil
  b3 = red (CONS (red (CONS TRUE (CONS TRUE NIL)))
           (CONS (red (CONS FALSE (CONS TRUE NIL))) 
           NIL))

  db12 : D tnil bool-list2
  db12 = gdiff b1 b2

  db13 : D tnil bool-list2
  db13 = gdiff b1 b3

  
