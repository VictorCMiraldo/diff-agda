\begin{code}
{-# OPTIONS --rewriting #-}
open import Prelude

open import Diffing.Universe
open import Diffing.Patches.Diff.D
open import Diffing.Patches.Diff.Cost
open import Diffing.Utils.Propositions

module Diffing.Patches.Diff.Id (Δ : Cost) where

  open import Diffing.Patches.Diff Δ
\end{code}

  It is easy to check whether a diff is the identity
  diff of a given element or not. 
  This is a simple decidable property

\begin{code}
  mutual
\end{code}
%<*Is-diff-id-type>
\begin{code}
    Is-diff-id : {n : ℕ}{t : T n}{ty : U n}
               → (d : D ⊥ₚ t ty) → Set
\end{code}
%</Is-diff-id-type>
\begin{code}
    Is-diff-id (D-A ())
    Is-diff-id D-unit = Unit
    Is-diff-id (D-inl p) = Is-diff-id p
    Is-diff-id (D-inr p) = Is-diff-id p
    Is-diff-id (D-setl x x₁) = ⊥
    Is-diff-id (D-setr x x₁) = ⊥
    Is-diff-id (D-pair p q) = Is-diff-id p × Is-diff-id q
    Is-diff-id (D-mu x) = Is-diffL-id x
    Is-diff-id (D-def p) = Is-diff-id p
    Is-diff-id (D-top p) = Is-diff-id p
    Is-diff-id (D-pop p) = Is-diff-id p
\end{code}
%<*Is-diffL-id-type>
\begin{code}
    Is-diffL-id : {n i j : ℕ}{t : T n}{ty : U (suc n)}
               → (d : Dμ ⊥ₚ t ty i j) → Set
\end{code}
%</Is-diffL-id-type>
\begin{code}
    Is-diffL-id Dμ-end = Unit
    Is-diffL-id (Dμ-A () p)
    Is-diffL-id (Dμ-ins x p) = ⊥
    Is-diffL-id (Dμ-del x p) = ⊥
    Is-diffL-id (Dμ-dwn dx dy p) = dx ≡ dy × Is-diffL-id p
\end{code}

  The identity patch is the same as (gdiff x x) but
  much easier to compute, as no comparisons are needed.

%<*gdiff-id-def>
\begin{code}
  -- {-# REWRITE μ-lal-sym #-}
  mutual
    gdiff-id : {n : ℕ}{t : T n}{ty : U n}
             → (a : ElU ty t) → Patch t ty
    gdiff-id unit = D-unit
    gdiff-id (inl a) = D-inl (gdiff-id a)
    gdiff-id (inr a) = D-inr (gdiff-id a)
    gdiff-id (a1 , a2) = D-pair (gdiff-id a1) (gdiff-id a2)
    gdiff-id (top a) = D-top (gdiff-id a)
    gdiff-id (pop a) = D-pop (gdiff-id a)
    gdiff-id (red a) = D-def (gdiff-id a)
    gdiff-id (mu a) = D-mu (gdiffL-id (mu a ∷ []))
  
    {-# TERMINATING #-}
    gdiffL-id : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (as : List (ElU (μ ty) t)) → Dμ ⊥ₚ t ty (length as) (length as)
    gdiffL-id [] = Dμ-end
    gdiffL-id (a ∷ as) = Dμ-dwn (μ-hd a) (μ-hd a) (gdiffL-id (μ-ch a ++ as))
\end{code}
%</gdiff-id-def>

\begin{code}
  mutual
\end{code}
%<*gdiff-id-correct-type>
\begin{code}
    gdiff-id-correct 
      : {n : ℕ}{t : T n}{ty : U n}
      → (a : ElU ty t) → gdiff-id a ≡ gdiff a a
\end{code}
%</gdiff-id-correct-type>
\begin{code}
    gdiff-id-correct unit = refl
    gdiff-id-correct (inl a) = cong D-inl (gdiff-id-correct a)
    gdiff-id-correct (inr a) = cong D-inr (gdiff-id-correct a)
    gdiff-id-correct (a1 , a2) 
      = cong₂ D-pair (gdiff-id-correct a1) (gdiff-id-correct a2)
    gdiff-id-correct (top a) = cong D-top (gdiff-id-correct a)
    gdiff-id-correct (pop a) = cong D-pop (gdiff-id-correct a)
    gdiff-id-correct (mu a) = cong D-mu (gdiffL-id-correct (mu a ∷ []))
    gdiff-id-correct (red a) = cong D-def (gdiff-id-correct a)

    {-# TERMINATING #-}
    gdiffL-id-correct
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (as : List (ElU (μ ty) t)) → gdiffL-id as ≡ gdiffL as as
    gdiffL-id-correct [] = refl
    gdiffL-id-correct (a ∷ as) 
      with costμ (gdiffL-del a as (a ∷ as)) ≤?-ℕ costμ (gdiffL-dwn a a as as) 
    ...| yes r1 
       rewrite sym (gdiff-id-correct (μ-hd a)) 
             | gdiff-id-cost (μ-hd a)
             | sym (gdiffL-id-correct (μ-ch a ++ as))
             | gdiffL-id-cost (μ-ch a ++ as)
             = ⊥-elim (nat-≤-abs-0 r1)
    ...| no ¬r1 
      with costμ (gdiffL-ins a (a ∷ as) as) ≤?-ℕ costμ (gdiffL-dwn a a as as) 
    ...| yes r2
        rewrite sym (gdiff-id-correct (μ-hd a)) 
             | gdiff-id-cost (μ-hd a)
             | sym (gdiffL-id-correct (μ-ch a ++ as))
             | gdiffL-id-cost (μ-ch a ++ as)
             = ⊥-elim (nat-≤-abs-0 r2)
    ...| no ¬r2 = cong (Dμ-dwn (μ-hd a) (μ-hd a)) (gdiffL-id-correct (μ-ch a ++ as))
\end{code}

  gdiff id has to have cost 0, as it is the identity.

%<*gdiff-id-cost-type>
\begin{code}
    gdiff-id-cost : {n : ℕ}{t : T n}{ty : U n}
                  → (a : ElU ty t) → cost (gdiff-id a) ≡ 0
\end{code}
%</gdiff-id-cost-type>
\begin{code}
    gdiff-id-cost unit = refl
    gdiff-id-cost (inl a) = gdiff-id-cost a
    gdiff-id-cost (inr a) = gdiff-id-cost a
    gdiff-id-cost (a1 , a2) 
      = subst (λ P → P + cost (gdiff-id a2) ≡ 0) 
              (sym (gdiff-id-cost a1)) (gdiff-id-cost a2)
    gdiff-id-cost (top a) = gdiff-id-cost a
    gdiff-id-cost (pop a) = gdiff-id-cost a
    gdiff-id-cost (mu a) = gdiffL-id-cost (mu a ∷ [])
    gdiff-id-cost (red a) = gdiff-id-cost a 

    {-# TERMINATING #-}
    gdiffL-id-cost : {n : ℕ}{t : T n}{ty : U (suc n)}
                  → (a : List (ElU (μ ty) t)) → costμ (gdiffL-id a) ≡ 0
    gdiffL-id-cost [] = refl
    gdiffL-id-cost (a ∷ as) 
      rewrite gdiffL-id-cost (μ-ch a ++ as)
            | sym (gdiff-id-correct (μ-hd a))
            | gdiff-id-cost (μ-hd a)
            = refl
\end{code}
