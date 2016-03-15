\begin{code}
open import Prelude
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties.Simple

open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.Ops
open import Diffing.Universe.MuUtils
open import Diffing.Universe.Measures
open import Diffing.Patches.Diff.D
open import Diffing.Utils.Propositions using (nat-≤-step; ≤-+)

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
  sum : ∀{a}{A : Set a}(f : A → ℕ)
      → List A → ℕ
  sum f = foldr (λ h r → f h + r) 0

  mutual
    {-# TERMINATING #-}
\end{code}
%<*cost-type>
\begin{code}
    cost : {n : ℕ}{t : Tel n}{ty : U n} → Patch t ty → ℕ
\end{code}
%</cost-type>
\begin{code}
    costL : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
          → Patchμ t ty → ℕ
    costL = sum costμ
\end{code}
%<*cost-def>
\begin{code}
    cost (D-A ())
    cost  D-unit        = 0
    cost (D-inl d)      = cost d
    cost (D-inr d)      = cost d
    cost (D-setl xa xb) = 2 * (sizeElU xa + sizeElU xb)
    cost (D-setr xa xb) = 2 * (sizeElU xa + sizeElU xb)
    cost (D-pair da db) = cost da + cost db
    cost (D-def d)   = cost d
    cost (D-top d) = cost d
    cost (D-pop d) = cost d
    cost (D-mu l)  = costL l
\end{code}
%</cost-def>


%<*costmu-type>
\begin{code}
    costμ : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
          → Dμ ⊥ₚ t ty → ℕ
\end{code}
%</costmu-type>
%<*costmu-def>
\begin{code}
    costμ (Dμ-A ())
    costμ (Dμ-ins x) = 1 + sizeElU x
    costμ (Dμ-del x) = 1 + sizeElU x
    costμ (Dμ-dwn x) = cost x
\end{code}
%</costmu-def>

\begin{code}
  infixr 20 _⊔_
  infixr 20 _⊔μ_
\end{code}

%<*lub-def>
\begin{code}
  _⊔_ : {n : ℕ}{t : Tel n}{ty : U n}
      → Patch t ty → Patch t ty → Patch t ty
  _⊔_ {ty = ty} da db with cost da ≤?-ℕ cost db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lub-def>

%<*lubmu-def>
\begin{code}
  _⊔μ_ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
      → Patchμ t ty → Patchμ t ty → Patchμ t ty
  _⊔μ_ da db with costL da ≤?-ℕ costL db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lubmu-def>

\begin{code}
  ⊔μ-elim : {n : ℕ}{t : Tel n}{ty : U (suc n)}{P : Patchμ t ty → Set}
          → (da db : Patchμ t ty)
          → P da → P db → P (da ⊔μ db)
  ⊔μ-elim da db pda pdb with costL da ≤?-ℕ costL db
  ...| yes _ = pda
  ...| no  _ = pdb
\end{code}
