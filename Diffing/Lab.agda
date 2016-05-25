open import Prelude
open import Prelude.Vector
open import CF
open import CF.Lab
open import CF.Operations.Derivative
open import CF.Operations.Vec
  using (chv)

open import Diffing.Patches.D
open import Diffing.Patches.Cost
open import Diffing.Patches.Diff top-down-cost
open import Diffing.Patches.Residual

module Diffing.Lab where

  ! : {A : Set} → Maybe A → A
  ! (just x) = x
  ! nothing  = magic
    where postulate magic : {A : Set} → A
  
  l1 l2 l3 l4 : ElU LIST (BOOL ∷ [])
  l1 = CONS TT (CONS TT (CONS FF NIL))
  l2 = CONS TT (CONS FF NIL)
  l3 = CONS TT (CONS FF (CONS FF NIL))
  l4 = CONS FF (CONS FF NIL)

  d12 d13 res123 : Patch LIST (BOOL ∷ [])
  d12 = gdiff l1 l2
  d13 = gdiff l1 l3

  res123 = (D-μ-dwn
      (D-inr (D-pair (D-pop (D-top (D-setl unit unit))) (D-top D-unit)))
      (D-μ-rmv (φ-right (φ-snd (pop (top (inl unit))) φ-hole))
       (D-μ-dwn
        (D-inr (D-pair (D-pop (D-top (D-inr D-unit))) (D-top D-unit)))
        (D-μ-dwn (D-inl D-unit) [] ∷ []))
       ∷ []))
  

  t1 t2 : ElU LTREE (BOOL ∷ NAT ∷ [])
  t1 = BRANCH TT
        (BRANCH FF (LEAF (SS (SS ZZ))) (LEAF ZZ))
        (LEAF (SS ZZ))


  t2 = BRANCH TT
        (LEAF (SS (SS ZZ)))
        (BRANCH FF (LEAF ZZ)
          (BRANCH FF (LEAF (SS (SS ZZ))) (LEAF ZZ)))

  -- !! takes about 1 minute to C-c C-n
  e12 : Patch LTREE (BOOL ∷ NAT ∷ [])
  e12 = gdiff t1 t2

  v1 v2 : ElU LTREE (BOOL ∷ u1 ∷ [])
  v1 = BRANCH TT
         (BRANCH TT
           (LEAF unit)
           (BRANCH TT
             (LEAF unit)
             (LEAF unit)))
         (LEAF unit)

  v2 = BRANCH FF
         (BRANCH FF
           (LEAF unit)
           (BRANCH FF
             (LEAF unit)
             (LEAF unit)))
         (LEAF unit)

  -- It takes long to compute, but
  -- it gives us the expected patch.
  f12 f12-nf : Patch LTREE (BOOL ∷ u1 ∷ [])
  f12 = gdiff v1 v2

  f12-nf = D-μ-dwn
          (D-inr
           (D-pair (D-pop (D-top (D-setl unit unit)))
            (D-pair (D-top D-unit) (D-top D-unit))))
          (D-μ-dwn
           (D-inr
            (D-pair (D-pop (D-top (D-setl unit unit)))
             (D-pair (D-top D-unit) (D-top D-unit))))
           (D-μ-dwn (D-inl (D-pop (D-pop (D-top D-unit)))) [] ∷
            D-μ-dwn
            (D-inr
             (D-pair (D-pop (D-top (D-setl unit unit)))
              (D-pair (D-top D-unit) (D-top D-unit))))
            (D-μ-dwn (D-inl (D-pop (D-pop (D-top D-unit)))) [] ∷
             D-μ-dwn (D-inl (D-pop (D-pop (D-top D-unit)))) [] ∷ [])
            ∷ [])
           ∷ D-μ-dwn (D-inl (D-pop (D-pop (D-top D-unit)))) [] ∷ [])

  
