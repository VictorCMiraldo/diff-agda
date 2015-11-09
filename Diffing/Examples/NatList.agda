open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Diff
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

  d1 : D tnil nat
  d1 = gdiff (to-nat-0 4) (to-nat-0 2)

  d2 : D tnil nat
  d2 = D-mu-del (inr (top void))
         (D-mu-del (inr (top void))
          (D-mu-del (inr (top void))
           (D-mu-del (inr (top void)) (D-mu-cpy (inl void) D-mu-end))))

  gapplyℕ : D tnil nat → ℕ → Maybe ℕ
  gapplyℕ d n with gapply d (to-nat-0 n)
  ...| nothing = nothing
  ...| just x  = just (to-ℕ x)

  -- Lists,
  list : {n : ℕ} → U (suc n)
  list = μ (u1 ⊕ (wk vl) ⊗ vl)

  NIL : {n : ℕ}{t : Tel (suc n)} → ElU list t
  NIL = mu (inl void)

  CONS : {n : ℕ}{a : U n}{t : Tel n} 
       → ElU a t → ElU list (tcons a t) → ElU list (tcons a t)
  CONS a as = mu (inr ((pop (top a)) , (top as)))

  -- Lists of nats
  nat-list : {n : ℕ} → U n
  nat-list = β list nat

  to-nat-list : List ℕ → ElU nat-list tnil
  to-nat-list [] = red NIL
  to-nat-list (x ∷ xs) with to-nat-list xs
  ...| (red (mu res)) = red (CONS (to-nat x) (mu res))

  l1 : ElU nat-list tnil
  l1 = to-nat-list (1 ∷ 2 ∷ [])

  l2 : ElU nat-list tnil
  l2 = to-nat-list (1 ∷ 6 ∷ [])

  d12 : D tnil nat-list
  d12 = gdiff l1 l2
