\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff
open import Diffing.Patches.Diff.Functor
open import Diffing.Patches.Residual
open import Diffing.Patches.Conflicts

open import Relation.Binary.PropositionalEquality 

module Diffing.Patches.Merging where
\end{code}

%<*merge>
\begin{code}
  merge : {n : ℕ}{t : Tel n}{ty : U n}
        → (d1 d2 : Patch t ty)
        → (C → Patch t ty)
        → Maybe (Patch t ty × Patch t ty)
  merge d1 d2 resolve 
    with d1 / d2 | inspect (_/_ d1) d2
  ...| nothing | _ = nothing
  ...| just d12 | [ R ] 
    with residual-symmetry-thm d1 d2 R
  ...| op , prf = {!D-map resolve d12!}
\end{code}
%</merge>
