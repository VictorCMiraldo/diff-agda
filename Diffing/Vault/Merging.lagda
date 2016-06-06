\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff
open import Diffing.Patches.Diff.Functor
open import Diffing.Patches.Overlap
open import Diffing.Patches.Residual
open import Diffing.Patches.Conflicts
open import Diffing.Patches.Merging.Grow

open import Data.List.All

open import Relation.Unary using (Decidable)

module Diffing.Patches.Merging where
\end{code}

\begin{code}
  freeGrow : {n : ℕ}{t : Tel n}{ty : U n}
           → D C t ty → D C t ty
  freeGrow d = partial-merge (D-map letGrow d)
    where
      letGrow : {n : ℕ}{t : Tel n}{ty : U n}
              → C t ty → Fewer C t ty
      letGrow (UpdUpd x y z) = i2 (UpdUpd x y z)
      letGrow (DelUpd x y)   = i2 (DelUpd x y)
      letGrow (UpdDel x y)   = i2 (UpdDel x y)
      letGrow (GrowL x)      = i1 (D-mu (Dμ-ins x ∷ []))
      letGrow (GrowR x)      = i1 (D-mu (Dμ-cpy x ∷ []))
      letGrow (GrowLR x y)   = i1 (D-mu (Dμ-cpy x ∷ Dμ-ins y ∷ []))

  gfilter : ∀{a}{A : Set a}{P : A → Set}
          → Decidable P → List A → Σ (List A) (All P)
  gfilter dp [] = [] , []
  gfilter dp (x ∷ l) with dp x
  ...| no  _   = gfilter dp l
  ...| yes prf = let (res , pres) = gfilter dp l
                 in x ∷ res , prf ∷ pres
  

  Δ : {n : ℕ}{t : Tel n}{ty : U n}
    → (p q : Patch t ty)(prf : Is-Just (p / q))
    → Σ (List (↓ C)) (All (↓-map IsGrow))
  Δ p q prf with p / q
  Δ p q ()          | nothing
  Δ p q (indeed .x) | just x 
    = gfilter (λ { (unIdx x) → IsGrow? x }) (forget x)

  
  
\end{code}
