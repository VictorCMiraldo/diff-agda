\begin{code}
open import Prelude
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties.Simple using (+-comm)

open import Diffing.Universe

module Diffing.Patches.Diff.Cost where
\end{code}

  A cost function is completely specified by the cost
  of a D-setl/D-setr and Dμ-ins/Dμ-del operations, 
  as long as they satisfy a few lemmas.

%<*Cost-rec>
\begin{code}
  record Cost : Set where
    constructor cost-rec
    field
      c⊕ : {n : ℕ}{t : T n}{x y : U n} → ElU x t → ElU y t → ℕ
      cμ : {n : ℕ}{t : T n}{x : U (suc n)} → ElU x (u1 ∷ t) → ℕ

      c⊕-sym-lemma : {n : ℕ}{t : T n}{x y : U n}
                   → (ex : ElU x t)(ey : ElU y t)
                   → c⊕ ex ey ≡ c⊕ ey ex
\end{code}
%</Cost-rec>

\begin{code}
  open Cost {{...}}
\end{code}

%<*top-down-cost-type>
\begin{code}
  top-down-cost : Cost
\end{code}
%</top-down-cost-type>
%<*top-down-cost-def>
\begin{code}
  top-down-cost 
    = cost-rec (λ ex ey → sizeElU ex + sizeElU ey) 
               sizeElU 
               (λ ex ey → (+-comm (sizeElU ex) (sizeElU ey)))
\end{code}
%</top-down-cost-def>


