open import Prelude
open import CF.Lab 
  using (LIST; CONS; NIL)
open import Diffing.Universe

module Diffing.Examples.Residual1 where

  open import Diffing.Patches.D
  open import Diffing.Patches.Properties.Alignment
  open import Diffing.Patches.Properties.WellFormed
  open import Diffing.Patches.Cost
  open import Diffing.Diff top-down-cost
  open import Diffing.Residual
  open import Diffing.Merger top-down-cost
  open import Diffing.Conflicts.C
  open import Diffing.Apply

  
  -- Quantum booleans (so we can have conflicts)
  QOOL : U 0
  QOOL = u1 ⊕ u1 ⊕ u1

  TT FF TF : ElU QOOL []
  TT = inl unit
  FF = inr (inl unit)
  TF = inr (inr unit)

  l1 l2 l3 : ElU LIST (QOOL ∷ [])
  l1 = CONS TT (CONS TT (CONS TT NIL))
  l2 = CONS TT (CONS FF (CONS TT NIL))
  l3 = CONS TT (CONS TT NIL)
  
  d12 : D ⊥ₚ (QOOL ∷ []) LIST
  d12 = gdiff l1 l2

  d13 : D ⊥ₚ (QOOL ∷ []) LIST
  d13 = gdiff l1 l3

  -- d12||d13 : d12 || d13
  -- d12||d13 = ||-intro ((gdiff-wf l1 l2 , gdiff-wf l1 l3) , refl)

  r23 : D C (QOOL ∷ []) LIST
  -- r23 = res d12 d13 d12||d13
  r23 = D-mu
       (Dμ-dwn
        (D-inr
         (D-pair (D-pop (D-top (D-setl unit (inl unit)))) (D-top D-unit)))
        ∷
        Dμ-dwn
        (D-inr (D-pair (D-pop (D-top (D-inl D-unit))) (D-top D-unit)))
        ∷ Dμ-dwn (D-inl D-unit) ∷ [])

  r32 : D C (QOOL ∷ []) LIST
  -- r32 = res d13 d12 (||-intro ((gdiff-wf l1 l3 , gdiff-wf l1 l2) , refl))
  r32 = D-mu
       (Dμ-del (inr (pop (top (inl unit)) , top unit)) ∷
        Dμ-dwn
        (D-inr
         (D-pair (D-pop (D-top (D-setl unit (inl unit)))) (D-top D-unit)))
        ∷
        Dμ-dwn
        (D-inr (D-pair (D-pop (D-top (D-inl D-unit))) (D-top D-unit)))
        ∷ Dμ-dwn (D-inl D-unit) ∷ [])

  r23-split : D ⊥ₚ (QOOL ∷ []) LIST × D ⊥ₚ (QOOL ∷ []) LIST
  r23-split = C-split r23

  
