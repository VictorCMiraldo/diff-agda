\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Ops
open import Diffing.Universe.MuUtils

module Diffing.Universe.Measures where
\end{code}

  It will be convenient to have some generic measures
  over our universe.

%<*countU>
\begin{code}
  countU : {n : ℕ} → Fin n → U n → ℕ
  countU i u0 = 0
  countU i u1 = 0
  countU i (a ⊕ b) = countU i a + countU i b
  countU i (a ⊗ b) = countU i a + countU i b
  countU i (β F x) = countU i x + countU (fs i) F
  countU i (μ u) = countU (fs i) u
  countU fz vl = 1
  countU (fs i) vl = 0
  countU fz (wk u) = 0
  countU (fs i) (wk u) = countU i u
\end{code}
%</countU>

%<*sizeU>
\begin{code}
  sizeU : {n : ℕ} → U n → ℕ
  sizeU u0 = 0
  sizeU u1 = 1
  sizeU (a ⊕ b) = sizeU a + sizeU b
  sizeU (a ⊗ b) = sizeU a * sizeU b
  sizeU (β F x) = sizeU x * countU fz F + sizeU F
  sizeU (μ u) = sizeU u
  sizeU vl = 1
  sizeU (wk u) = sizeU u
\end{code}
%</sizeU>

\begin{code}
  {-# TERMINATING #-}
\end{code}
%<*sizeEl>
\begin{code}
  sizeElU : {n : ℕ}{t : Tel n}{u : U n} → ElU u t → ℕ
  sizeElU void        = 1
  sizeElU (inl el)    = 1 + sizeElU el
  sizeElU (inr el)    = 1 + sizeElU el
  sizeElU (ela , elb) = sizeElU ela + sizeElU elb
  sizeElU (top el)    = sizeElU el
  sizeElU (pop el)    = sizeElU el
  sizeElU (mu el)
    = let (hdE , chE) = μ-open (mu el)
      in sizeElU hdE + foldr _+_ 0 (map sizeElU chE)
  sizeElU (red el)    = sizeElU el
\end{code}
%</sizeEl>
