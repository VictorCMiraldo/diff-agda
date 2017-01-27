\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Patches.Cost
open import Diffing.Patches.Properties.WellFormed
open import Diffing.Patches.D
open import Diffing.Patches.Functor
open import Diffing.Conflicts.C

module Diffing.Merger (Δ : Cost) where

  open import Diffing.Diff Δ
\end{code}

  An interesting aspect over Conflicts is that
  we can always generate two patches from a conflict!

%<*C-prod-def>
\begin{code}
  C-prod : {n : ℕ}{t : T n}{ty : U n}
         → C t ty → (D ⊥ₚ t ty × D ⊥ₚ t ty)
  C-prod (UpdUpd o x y) = gdiff o x , gdiff o y
  C-prod (DelUpd x y)   = (D-mu (Dμ-del x ∷ [])) , (D-mu (Dμ-dwn (gdiff x y) ∷ []))
  C-prod (UpdDel x y)   = (D-mu (Dμ-dwn (gdiff x y) ∷ [])) , (D-mu (Dμ-del y ∷ []))
  C-prod (GrowL x)      = (D-mu (Dμ-ins x ∷ [])) , (D-mu [])
  C-prod (GrowLR x y)   = (D-mu (Dμ-ins x ∷ [])) , (D-mu (Dμ-ins y ∷ []))
  C-prod (GrowR x)      = (D-mu []) , (D-mu (Dμ-ins x ∷ []))
\end{code}
%</C-prod-def>

  Combining that with some monadic functionaliy of D,
  we get:

\begin{code}
  C-split : {n : ℕ}{t : T n}{ty : U n}
          → D C t ty → D ⊥ₚ t ty × D ⊥ₚ t ty
  C-split = (D-mult ×' D-mult) ∘ D-delta ∘ D-map C-prod
\end{code}
