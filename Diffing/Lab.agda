open import Prelude
open import Prelude.Vector
open import CF
open import CF.Lab
open import CF.Derivative.Operations
open import CF.Operations.Properties
  using (ch-v)

open import Diffing.Patches.D
open import Diffing.Patches.Cost
open import Diffing.Patches.Diff top-down-cost

module Diffing.Lab where

  
  l1 l2 : ElU LIST (BOOL ∷ [])
  l1 = CONS TT (CONS TT (CONS FF NIL))
  l2 = CONS TT (CONS FF NIL)

  d12 : Patch LIST (BOOL ∷ [])
  d12 = gdiff l1 l2

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

  f12-nf = D-μ-dwn (inr (pop (top (inl unit)) , (top unit , top unit)))
          (inr (pop (top (inr unit)) , (top unit , top unit))) refl
          (D-μ-dwn (inr (pop (top (inl unit)) , (top unit , top unit)))
           (inr (pop (top (inr unit)) , (top unit , top unit))) refl
           (D-μ-dwn (inl (pop (pop (top unit)))) (inl (pop (pop (top unit))))
            refl []
            ∷
            D-μ-dwn (inr (pop (top (inl unit)) , (top unit , top unit)))
            (inr (pop (top (inr unit)) , (top unit , top unit))) refl
            (D-μ-dwn (inl (pop (pop (top unit)))) (inl (pop (pop (top unit))))
             refl []
             ∷
             D-μ-dwn (inl (pop (pop (top unit)))) (inl (pop (pop (top unit))))
             refl []
             ∷ [])
            ∷ [])
           ∷
           D-μ-dwn (inl (pop (pop (top unit)))) (inl (pop (pop (top unit))))
           refl []
           ∷ [])

  
