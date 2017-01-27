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

module Diffing.Patches.Conflicts.Grow where
\end{code}

  As we mentioned before, grow conflicts can be made simpler.
  We can, given two patches d1 d2, allow growing in both directions.

\begin{code}
  allow-grow : {n : ℕ}{t : Tel n}{ty : U n}{k : D C t ty}
              → (d1 d2 : Patch t ty)
              → d1 / d2 ≡ just k
              → D (Fewer C) t ty
  allow-grow d1 d2 prf
    with d1 / d2
  allow-grow d1 d2 () | nothing
  allow-grow d1 d2 _  | just d12
    = D-map solve-grow d12
    where
      solve-grow : {n : ℕ}{t : Tel n}{ty : U n}
                  → C t ty → Fewer C t ty
      solve-grow (GrowR x) = i1 (D-mu (Dμ-cpy x ∷ []))
      solve-grow (GrowL x) = i1 (D-mu (Dμ-ins x ∷ []))
      solve-grow c         = i2 c
      -- TODO: How to handle GrowLR? We need a total order over (ElU ty t)
\end{code}
