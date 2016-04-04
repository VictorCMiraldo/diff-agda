\begin{code}
{-# OPTIONS --rewriting #-}
open import Prelude
open import Diffing.Universe
open import Diffing.Utils.Vector
open import Diffing.Patches.Diff.Cost
open import Diffing.Patches.Diff.D

module Diffing.Patches.Diff (Δ : Cost)
  where

  open Cost
\end{code}

            Diffing
  ===========================

  We start by introducing a "generic" notion of cost. 

\begin{code}
  infixr 20 _⊓_
  infixr 20 _⊓μ_
\end{code}

%<*gdiff-type>
\begin{code}
  {-# TERMINATING #-}
  gdiff : {n : ℕ}{t : T n}{ty : U n} 
        → ElU ty t → ElU ty t → Patch t ty
\end{code}
%</gdiff-type>

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
    cost (D-setl xa xb) = c⊕ Δ xa xb
    cost (D-setr xa xb) = c⊕ Δ xb xa
    cost (D-pair da db) = cost da + cost db
    cost (D-def d) = cost d
    cost (D-top d) = cost d
    cost (D-pop d) = cost d
    cost (D-mu l)  = costμ l

    costμ : {n i j : ℕ}{t : T n}{ty : U (suc n)} → Dμ ⊥ₚ t ty i j → ℕ
    costμ (Dμ-A () d)  
    costμ (Dμ-ins x d) = cμ Δ x + costμ d
    costμ (Dμ-del x d) = cμ Δ x + costμ d
    costμ (Dμ-dwn x y d) = cost (gdiff x y) + costμ d
    costμ Dμ-end = 0
\end{code}
%</cost-def>

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

%<*gdiffL-type>
\begin{code}
  gdiffL : {n : ℕ}{t : T n}{ty : U (suc n)} 
         → (xs ys : List (ElU (μ ty) t)) → Dμ ⊥ₚ t ty (length xs) (length ys)
\end{code}
%</gdiffL-type>

  Before the actual diffing algorithm, we still need
  to populate our bag of tricks.

  Now we can define auxiliar functions for computing recursive diffs
  AND taking care of their indicies.

\begin{code}
  {-# REWRITE μ-lal-sym #-}
  gdiffL-ins : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (length xs) (suc (length ys))
  gdiffL-ins y xs ys = Dμ-ins (μ-hd y) (gdiffL xs (μ-ch y ++ ys))

  gdiffL-del : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (suc (length xs)) (length ys)
  gdiffL-del x xs ys = Dμ-del (μ-hd x) (gdiffL (μ-ch x ++ xs) ys)

  gdiffL-dwn : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (suc (length xs)) (suc (length ys))
  gdiffL-dwn x y xs ys 
    = Dμ-dwn (μ-hd x) (μ-hd y) (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys))
\end{code}

  Finally, the actual diffing algorithm.

%<*gdiff-def>
\begin{code}
  gdiff {ty = var} (top a) (top b)    = D-top (gdiff a b)
  gdiff {ty = wk u} (pop a) (pop b)  = D-pop (gdiff a b)
  gdiff {ty = def F x} (red a) (red b) = D-def (gdiff a b)
  gdiff {ty = u1} unit unit = D-unit
  gdiff {ty = ty ⊗ tv} (ay , av) (by , bv) 
    = D-pair (gdiff ay by) (gdiff av bv)
  gdiff {ty = ty ⊕ tv} (inl ay) (inl by) = D-inl (gdiff ay by)
  gdiff {ty = ty ⊕ tv} (inr av) (inr bv) = D-inr (gdiff av bv)
  gdiff {ty = ty ⊕ tv} (inl ay) (inr bv) = D-setl ay bv
  gdiff {ty = ty ⊕ tv} (inr av) (inl by) = D-setr av by
  gdiff {ty = μ ty} a b = D-mu (gdiffL (a ∷ []) (b ∷ []))
\end{code}
%</gdiff-def>
%<*gdiffL-def>
\begin{code}
  gdiffL [] [] = Dμ-end
  gdiffL [] (y ∷ ys) = gdiffL-ins y [] ys
  gdiffL (x ∷ xs) [] = gdiffL-del x xs [] 
  gdiffL (x ∷ xs) (y ∷ ys) 
    =  gdiffL-ins y (x ∷ xs) ys 
    ⊓μ gdiffL-del x xs (y ∷ ys)
    ⊓μ gdiffL-dwn x y xs ys
\end{code}
%</gdiffL-def>
