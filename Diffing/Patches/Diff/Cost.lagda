\begin{code}
open import Prelude
open import Data.Nat using (_≤_; z≤n; s≤s)

open import Diffing.Universe
open import Diffing.Patches.Diff.D

module Diffing.Patches.Diff.Cost where
\end{code}


  The cost function is trivial for the non-inductive types.
  The inductive types are a bit trickier, though.
  We want our diff to have maximum sharing, that means
  we seek to copy most of the information we see.
  However, there are two obvious ways of copying:

    (D-mu-cpy x d) ∨ (D-mu-down (diff x x) d)

  We want the first one to be chosen.
  Which means, 
  
    cost (D-mu-cpy x d) < cost (D-mu-down (diff x x) d)
  ↔         k + cost d  < cost (diff x x) + 1 + cost d
  ⇐                  k  < cost (diff x x) + 1
  
  However, diff x x will basically be copying every constructor of x,
  which is intuitively the size of x. We then define the cost of
  copying x to be 0.

  Inserting and deleting, on the other hand, must be more
  expensive than making structural changes (when possible!)
  The same reasoning applies to the fact that we prefer copying
  over inserting and deleting.

    D-mu-cpy x d ≈ D-mu-down (diff x x) d ≈ D-mu-ins x (D-mu-del x d)
  
  With this in mind, we implement the cost function as follows:

\begin{code}
  mutual
    {-# TERMINATING #-}
\end{code}
%<*cost-def>
\begin{code}
    cost : {n : ℕ}{t : T n}{ty : U n} → Patch t ty → ℕ
    cost (D-A ())
    cost D-unit         = 0
    cost (D-inl d)      = cost d
    cost (D-inr d)      = cost d
    cost (D-setl xa xb) = 2 * (sizeElU xa + sizeElU xb)
    cost (D-setr xa xb) = 2 * (sizeElU xa + sizeElU xb)
    cost (D-pair da db) = cost da + cost db
    cost (D-def d) = cost d
    cost (D-top d) = cost d
    cost (D-pop d) = cost d
    cost (D-mu l)  = costμ l

    costμ : {n i j : ℕ}{t : T n}{ty : U (suc n)} → Dμ ⊥ₚ t ty i j → ℕ
    costμ (Dμ-A () d)  
    costμ (Dμ-ins x d) = 1 + sizeElU x + costμ d
    costμ (Dμ-del x d) = 1 + sizeElU x + costμ d
    costμ (Dμ-dwn x d) = cost x + costμ d
    costμ Dμ-end = 0
\end{code}
%</cost-def>

\begin{code}
  infixr 20 _⊓_
  infixr 20 _⊓μ_
\end{code}

%<*lub-def>
\begin{code}
  _⊓_ : {n : ℕ}{t : T n}{ty : U n}
      → Patch t ty → Patch t ty → Patch t ty
  _⊓_ {ty = ty} da db with cost da ≤?-ℕ cost db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lub-def>

%<*lubmu-def>
\begin{code}
  _⊓μ_ : {n i j : ℕ}{t : T n}{ty : U (suc n)}
      → Dμ ⊥ₚ t ty i j → Dμ ⊥ₚ t ty i j → Dμ ⊥ₚ t ty i j
  _⊓μ_ da db with costμ da ≤?-ℕ costμ db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lubmu-def>

\begin{code}
  ⊓μ-elim : {n i j : ℕ}{t : T n}{ty : U (suc n)}{P : {i j : ℕ} → Dμ ⊥ₚ t ty i j → Set}
          → (da db : Dμ ⊥ₚ t ty i j)
          → P da → P db → P (da ⊓μ db)
  ⊓μ-elim da db pda pdb with costμ da ≤?-ℕ costμ db
  ...| yes _ = pda
  ...| no  _ = pdb

  ⊓μ-elim3 : {n i j : ℕ}{t : T n}{ty : U (suc n)}{P : {i j : ℕ} → Dμ ⊥ₚ t ty i j → Set}
           → (da db dc : Dμ ⊥ₚ t ty i j)
           → P da → P db → P dc → P (da ⊓μ (db ⊓μ dc))
  ⊓μ-elim3 {P = P} da db dc pda pdb pdc
    = ⊓μ-elim {P = P} da (db ⊓μ dc) pda (
        ⊓μ-elim {P = P} db dc pdb pdc)
      

  ⊓μ-elim-imp 
    : {n i j : ℕ}{t : T n}{ty : U (suc n)}{P : {i j : ℕ} → Dμ ⊥ₚ t ty i j → Set}
      {da db : Dμ ⊥ₚ t ty i j}
    → P da → P db → P (da ⊓μ db)
  ⊓μ-elim-imp {P = P} {da} {db} pda pdb = ⊓μ-elim {P = P} da db pda pdb
\end{code}
