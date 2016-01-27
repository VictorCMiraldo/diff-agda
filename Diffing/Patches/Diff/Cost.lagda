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
  mutual
    {-# TERMINATING #-}
\end{code}
%<*cost-def>
\begin{code}
    cost : {n : ℕ}{t : Tel n}{ty : U n} → Patch t ty → ℕ
    cost (D-A ())
    cost  D-void        = 1
    cost (D-inl d)      = 1 + cost d
    cost (D-inr d)      = 1 + cost d
    cost (D-setl xa xb) = 2 * (sizeElU xa + sizeElU xb)
    cost (D-setr xa xb) = 2 * (sizeElU xa + sizeElU xb)
    cost (D-pair da db) = cost da + cost db
    cost (D-β d)   = cost d
    cost (D-top d) = cost d
    cost (D-pop d) = cost d
    cost (D-mu l)  = foldr (λ h r → costμ h + r) 0 l

    costμ : {n : ℕ}{t : Tel n}{ty : U (suc n)} → Dμ ⊥ₚ t ty → ℕ
    costμ (Dμ-A ())
    costμ (Dμ-ins x) = sizeElU x + 1
    costμ (Dμ-del x) = sizeElU x + 1
    costμ (Dμ-cpy x) = 0
    costμ (Dμ-dwn x) = cost x
\end{code}
%</cost-def>

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

\begin{code}
  paIsFirst : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            → Patchμ t ty → Patchμ t ty → Bool
  paIsFirst [] [] = true
  paIsFirst [] (x ∷ pb) = false
  paIsFirst (x ∷ pa) [] = true
  paIsFirst (Dμ-A () ∷ pa) _
  paIsFirst _ (Dμ-A () ∷ pb)
  paIsFirst (Dμ-dwn _ ∷ pa) (Dμ-dwn _ ∷ pb) = paIsFirst pa pb
  paIsFirst (Dμ-dwn _ ∷ pa) (_ ∷ _) = true
  paIsFirst (_ ∷ _) (Dμ-dwn _ ∷ pb) = false
  paIsFirst (x ∷ pa) (y ∷ pb)       = paIsFirst pa pb
\end{code}

%<*lubmu-def>
\begin{code}
  _⊔μ_ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
      → Patchμ t ty → Patchμ t ty → Patchμ t ty
  _⊔μ_ {ty = ty} da db with cost (D-mu da) ≤?-ℕ cost (D-mu db)
  ...| no  _ = db
  ...| yes _ with cost (D-mu da) ≟-ℕ cost (D-mu db)
  ...| no  _ = da
  ...| yes _ with paIsFirst da db
  ...| true  = da
  ...| false = db
\end{code}
%</lubmu-def>
