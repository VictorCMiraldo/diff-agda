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
  mutual
\end{code}
\begin{code}
    {-# TERMINATING #-}
    gapply : {n : ℕ}{t : T n}{ty : U n}
           → (p : Patch ty t)(x : ElU ty t)
           → Maybe (ElU ty t)
\end{code}
\begin{code}
    gapply-correct
      : {n : ℕ}{t : T n}{ty : U n}
      → (p : Patch ty t)
      → gapply p (D-src p) ≡ just (D-dst p)
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
      with gapply p (fgt 0 x) | inspect (gapply p) (fgt 0 x)
    ...| nothing | _ = nothing
    ...| just x' | [ R ]
       = (mu ∘ plugv 0 x')
         <M> vmapM (λ { (q₀ , pop x₀) → pop <M> gapply q₀ x₀ })
                   (vec-reindx (trans (D-ar-dst-lemma 0 p) (cong (ar 0) refl))
                   (vzip (trans (D-ar-dst-lemma 0 p) (cong (ar 0) refl)) q (chv 0 x)))
\end{code}

\begin{code}
    gapply-correct (D-A x) = {!!}
    gapply-correct D-unit = {!!}
    gapply-correct (D-inl p) = {!!}
    gapply-correct (D-inr p) = {!!}
    gapply-correct (D-setl x x₁) = {!!}
    gapply-correct (D-setr x x₁) = {!!}
    gapply-correct (D-pair p p₁) = {!!}
    gapply-correct (D-μ-dwn p hi ho x) = {!!}
    gapply-correct (D-μ-add x p) = {!!}
    gapply-correct (D-μ-rmv x p) = {!!}
    gapply-correct (D-def p) = {!!}
    gapply-correct (D-top p) = {!!}
    gapply-correct (D-pop p) = {!!}
\end{code}
