\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff

module Diffing.Patches.Diff.Properties where
\end{code}

%<*DiscreteEq>
\begin{code}
  _≈-M_ : {A B : Set} → Maybe A → Maybe B → Set
  (just _) ≈-M (just _) = Unit
  nothing  ≈-M nothing  = Unit
  _        ≈-M _        = ⊥
\end{code}
%</DiscreteEq>

%<*Aligned>
\begin{code}
  Aligned : {n : ℕ}{t : Tel n}{ty : U n}
          → (d1 d2 : D t ty) → Set
  Aligned {n} {t} {ty} d1 d2 
    = (x : ElU ty t) → (gapply d1 x) ≈-M (gapply d2 x)
\end{code}
%</Aligned>

%<*AlignedL>
\begin{code}
  AlignedL : {n : ℕ}{t : Tel n}{ty : U (suc n)}
           → (d1 d2 : List (Dμ t ty)) → Set
  AlignedL {n} {t} {ty} d1 d2 
    = (x : List (ElU (μ ty) t)) → (gapplyL d1 x) ≈-M (gapplyL d2 x)
\end{code}
%</AlignedL>

%<*AlignedL-elim-lemmas>
\begin{code}
  alignedL-nil-nil : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                  → AlignedL {t = t} {ty = ty} [] []
  alignedL-nil-nil x = unit

  alignedL-del-elim : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                → {d1 d2 : List (Dμ t ty)}
                → AlignedL d1 d2 → AlignedL d1 (Dμ-del _ ∷ d2) → ⊥
  alignedL-del-elim a b with b []
  ...| r = {!!}
