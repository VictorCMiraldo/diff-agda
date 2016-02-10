\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Patches.Diff hiding (Dμ)

module Diffing.Postulated where

  postulate T : ∀{a}{A : Set a} → A
\end{code}

This is a simple module for us to speed up typechecking the paper.
All the complicated results are to be postulated here.

%<*gdiff-correctness>
\begin{code}
  correctness : {n : ℕ}{t : Tel n}{ty : U n}
              → (a b : ElU ty t)
              → gapply (gdiff a b) a ≡ just b
\end{code}
%</gdiff-correctness>
\begin{code}
  correctness = T
\end{code}

%<*Dmu-type-safe-type>
\begin{code}
  data Dμ {a}(A : {n : ℕ} → Tel n → U n → Set a)
          {n : ℕ}(t : Tel n)(ty : U (suc n))
       : ℕ → ℕ → Set where
\end{code}
%</Dmu-type-safe-type>
