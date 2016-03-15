\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Patches.Diff hiding (Dμ; D)

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

%<*D-type>
\begin{code}
  data D (A : {n : ℕ} → Tel n → U n → Set) 
    : {n : ℕ} → Tel n → U n → Set where
\end{code}
%</D-type>

%<*Dmu-type>
\begin{code}
  data Dμ (A : {n : ℕ} → Tel n → U n → Set) 
    : {n : ℕ} → Tel n → U (suc n) → Set where
\end{code}
%</Dmu-type>

%<*Dmu-type-safe-type>
\begin{code}
  data Dμ₂ (A : {n : ℕ} → Tel n → U n → Set)
           {n : ℕ}(t : Tel n)(ty : U (suc n))
       : ℕ → ℕ → Set where
\end{code}
%</Dmu-type-safe-type>
