open import Prelude
open import Diffing.Universe

module Diffing.Examples.NatList where

  open import Diffing.Patches.D
  open import Diffing.Patches.Properties.Alignment
  open import Diffing.Patches.Properties.WellFormed
  open import Diffing.Patches.Cost
  open import Diffing.Diff top-down-cost
  open import Diffing.Residual
  open import Diffing.Merger top-down-cost
  open import Diffing.Conflicts.C
  open import Diffing.Apply

  -- Natural numbers,
  nat : {n : ℕ} → U n
  nat = μ (u1 ⊕ var)

  -- Z : {n : ℕ}{t : Tel n} → ElU nat t
  pattern Z = mu (inl unit)

  -- S : {n : ℕ}{t : Tel n} → ElU nat t → ElU nat t
  pattern S n = mu (inr (top n))

  to-nat : {n : ℕ}{t : T n} → ℕ → ElU nat t
  to-nat zero = Z
  to-nat (suc x) = S (to-nat x)

  to-ℕ : {n : ℕ}{t : T n} → ElU nat t → ℕ
  to-ℕ Z = zero
  to-ℕ (S n) = suc (to-ℕ n)

  to-nat-0 : ℕ → ElU nat []
  to-nat-0 = to-nat

  gapplyℕ : D ⊥ₚ [] nat → ℕ → Maybe ℕ
  gapplyℕ d n with gapply d (to-nat-0 n)
  ...| nothing = nothing
  ...| just x  = just (to-ℕ x)

  -- Lists,
  list : {n : ℕ} → U (suc n)
  list = μ (u1 ⊕ (wk var) ⊗ var)

  -- NIL : {n : ℕ}{t : Tel (suc n)} → ElU list t
  pattern NIL = mu (inl unit)

  -- CONS : {n : ℕ}{a : U n}{t : Tel n} 
  --     → ElU a t → ElU list (tcons a t) → ElU list (tcons a t)
  pattern CONS a as = mu (inr ((pop (top a)) , (top as)))

  -- Lists of nats
  nat-list : {n : ℕ} → U n
  nat-list = def list nat

  to-nat-list : List ℕ → ElU nat-list []
  to-nat-list [] = red NIL
  to-nat-list (x ∷ xs) with to-nat-list xs
  ...| (red (mu res)) = red (CONS (to-nat x) (mu res))

  from-nat-list : ElU nat-list [] → List ℕ
  from-nat-list (red NIL) = []
  from-nat-list (red (CONS x xs)) = to-ℕ x ∷ from-nat-list (red xs)

  l1 : ElU nat-list []
  l1 = to-nat-list (1 ∷ 2 ∷ [])

  l2 : ElU nat-list []
  l2 = to-nat-list (1 ∷ 6 ∷ [])

  l3 : ElU nat-list []
  l3 = to-nat-list (2 ∷ 4 ∷ 1 ∷ [])

  d12 : Patch [] nat-list
  d12 = gdiff l1 l2

  d13 : Patch [] nat-list
  d13 = gdiff l1 l3

  -- booleans
  bool : {n : ℕ} → U n
  bool = u1 ⊕ u1

  pattern TRUE = inl unit
  pattern FALSE = inr unit

 -- quantum booleans

  qool : {n : ℕ} → U n
  qool = bool ⊕ u1

  pattern QTRUE  = inl TRUE
  pattern QFALSE = inl FALSE
  pattern QBOTH  = inr unit

  Δ : {n : ℕ} → U (suc n)
  Δ = var ⊗ var

  m1 : ElU (def Δ qool) []
  m1 = red ((top QTRUE) , (top QTRUE))

  m2 : ElU (def Δ qool) []
  m2 = red (top QFALSE , top QTRUE)

  m3 : ElU (def Δ qool) []
  m3 = red ((top QTRUE) , (top QFALSE))

  m4 : ElU (def Δ qool) []
  m4 = red ((top QBOTH) , (top QTRUE))

  bp1 : Patch [] (def Δ qool)
  bp1 = gdiff m1 m2

  bp2 : Patch [] (def Δ qool)
  bp2 = gdiff m1 m3

  bp3 : Patch [] (def Δ qool)
  bp3 = gdiff m1 m4


  -- List of Bools
  bool-list2 : {n : ℕ} → U n
  bool-list2 = def list (def list bool)

  b1 : ElU bool-list2 []
  b1 = red (CONS (red (CONS TRUE (CONS FALSE NIL))) 
           (CONS (red (CONS FALSE NIL)) 
           NIL))

  b2 : ElU bool-list2 []
  b2 = red (CONS (red (CONS TRUE (CONS FALSE NIL))) 
           (CONS (red (CONS FALSE NIL)) 
           (CONS (red NIL) 
           NIL)))

  b2' : ElU bool-list2 []
  b2' = red (CONS (red (CONS TRUE NIL)) 
           (CONS (red (CONS FALSE NIL)) 
           (CONS (red NIL) 
           NIL)))

  b3 : ElU bool-list2 []
  b3 = red (CONS (red (CONS TRUE (CONS TRUE NIL)))
           (CONS (red (CONS FALSE (CONS TRUE NIL))) 
           NIL))

  db12 : Patch [] bool-list2
  db12 = gdiff b1 b2

  db13 : Patch [] bool-list2
  db13 = gdiff b1 b3

  
