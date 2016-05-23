\begin{code}
open import Prelude
open import Prelude.Vector

open import Diffing.CF-base
open import CF.Derivative
  using (match; _◂_)
open import Diffing.Patches.D

module Diffing.Patches.Apply where
\end{code}

\begin{code}
  {-# TERMINATING #-}
  gapply : {n : ℕ}{t : T n}{ty : U n}
         → (p : Patch ty t)(x : ElU ty t)
         → Maybe (ElU ty t)
\end{code}
\begin{code}
  gapply (D-A ()) x
  gapply D-unit unit = just unit
  gapply (D-inl p) x = {!!}
  gapply (D-inr p) x = {!!}
  gapply (D-setl p q) x = {!!}
  gapply (D-setr p q) x = {!!}
  gapply (D-pair p q) x = {!!}
  gapply (D-def p) x = {!!}
  gapply (D-top p) x = {!!}
  gapply (D-pop p) x = {!!}
  gapply (D-μ-add ctx p) x
    = (mu ∘ _◂_ ctx ∘ pop) <M>  gapply p x
  gapply (D-μ-rmv ctx p) (mu x)
    with match ctx x
  ...| nothing = nothing
  ...| just (pop x') = gapply p x'
  gapply (D-μ-dwn p hi refl q) (mu x)
    with gapply p (fgt 0 x)
  ...| nothing = nothing
  ...| just x'
     = (mu ∘ plugv 0 x')
       <M> vmapM (λ { (q₀ , pop x₀) → pop <M> gapply q₀ x₀ })
                 (vec-reindx {!!} (vzip {!!} q (chv 0 x)))
\end{code}
