open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Patches1.Diff
open import Diffing.Patches1.Residual
open import Diffing.Patches1.Conflicts
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

  gapplyℕ : Patch tnil nat → ℕ → Maybe ℕ
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

  d12 : Patch tnil nat-list
  d12 = gdiff l1 l2

  d13 : Patch tnil nat-list
  d13 = gdiff l1 l3

  -- booleans
  bool : {n : ℕ} → U n
  bool = u1 ⊕ u1

  pattern TRUE = inl void
  pattern FALSE = inr void

 -- quantum booleans

  qool : {n : ℕ} → U n
  qool = bool ⊕ u1

  pattern QTRUE  = inl TRUE
  pattern QFALSE = inl FALSE
  pattern QBOTH  = inr void

  Δ : {n : ℕ} → U (suc n)
  Δ = vl ⊗ vl

  m1 : ElU (β Δ qool) tnil
  m1 = red ((top QTRUE) , (top QTRUE))

  m2 : ElU (β Δ qool) tnil
  m2 = red (top QFALSE , top QTRUE)

  m3 : ElU (β Δ qool) tnil
  m3 = red ((top QTRUE) , (top QFALSE))

  m4 : ElU (β Δ qool) tnil
  m4 = red ((top QBOTH) , (top QTRUE))

  bp1 : Patch tnil (β Δ qool)
  bp1 = gdiff m1 m2

  bp2 : Patch tnil (β Δ qool)
  bp2 = gdiff m1 m3

  bp3 : Patch tnil (β Δ qool)
  bp3 = gdiff m1 m4


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

  _==_ : {n : ℕ}{t : Tel n}{ty : U n}
       → (a b : Maybe (ElU ty t)) → Bool
  nothing == nothing = true
  just d  == just e with d ≟-U e
  ...| yes _ = true
  ...| no  _ = false
  _ == _ = false

  db12 : Patch tnil bool-list2
  db12 = gdiff b1 b2

  db12nf : Patch tnil bool-list2
  db12nf = nf db12

  db13 : Patch tnil bool-list2
  db13 = gdiff b1 b3

  
