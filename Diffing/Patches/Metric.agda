open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Patches.Diff

open import Relation.Binary.PropositionalEquality

module Diffing.Patches.Metric where

  _-_ : {n : ℕ}{t : Tel n}{ty : U n}
      → ElU ty t → ElU ty t → ℕ
  a - b = cost (gdiff a b)

  cons : {n : ℕ}{t : Tel n}{a : U n}
       → ElU a t → ElU list (tcons a t) → ElU list (tcons a t)
  cons hd tl = mu (inr ((pop (top hd)) , (top tl)))

  nil : {n : ℕ}{t : Tel (suc n)}
      → ElU list t
  nil = mu (inl unit)

  bool : {n : ℕ} → U n
  bool = u1 ⊕ u1

  bT : {n : ℕ}{t : Tel n} → ElU bool t
  bT = inl unit

  bF : {n : ℕ}{t : Tel n} → ElU bool t
  bF = inr unit

  l1 : ElU list (tcons list (tcons bool tnil))
  l1 = cons (cons bF nil) nil

  l2 : ElU list (tcons list (tcons bool tnil))
  l2 = cons (cons bT nil) nil

  
