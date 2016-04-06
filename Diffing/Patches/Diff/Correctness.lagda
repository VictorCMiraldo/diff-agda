\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Patches.Diff.Cost
open import Diffing.Patches.Diff.D
open import Diffing.Patches.Diff
open import Diffing.Patches.Apply

module Diffing.Patches.Diff.Correctness where
\end{code}

%<*diff-correctness-type>
\begin{code}
  diff-correctness : {Δ : Cost}{n : ℕ}{t : T n}{ty : U n}
                   → (x y : ElU ty t)
                   → gapply (gdiff Δ x y) x ≡ just y
\end{code}
%</diff-correctness-type>
%<*diff-correctness-def>
\begin{code}
  diff-correctness {Δ} x y 
    = trans (cong (gapply (gdiff Δ x y)) (sym (gdiff-src-lemma Δ x y))) 
            (sym (trans (cong just (sym (gdiff-dst-lemma Δ x y))) 
                        (sym (gapply-correct (gdiff Δ x y)))))
\end{code}
%</diff-correctness-def>










