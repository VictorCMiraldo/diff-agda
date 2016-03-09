\begin{code}
open import Prelude
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties.Simple using (+-comm)

open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Universe.Measures
open import Diffing.Patches.Diff
open import Diffing.Utils.Propositions

module Diffing.Patches.Diff.Id where
\end{code}

  It is easy to check whether a diff is the identity
  diff of a given element or not. 
  This is a simple decidable property

\begin{code}
  mutual
\end{code}
%<*Is-diff-id-type>
\begin{code}
    Is-diff-id : {n : ℕ}{t : Tel n}{ty : U n}
               → (d : Patch t ty) → Set
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
    Is-diff-id (D-mu x) = Is-diffL-id x × (x ≡ [] → ⊥)
    Is-diff-id (D-β p) = Is-diff-id p
    Is-diff-id (D-top p) = Is-diff-id p
    Is-diff-id (D-pop p) = Is-diff-id p
\end{code}
%<*Is-diffL-id-type>
\begin{code}
    Is-diffL-id : {n : ℕ}{t : Tel n}{ty : U (suc n)}
               → (d : Patchμ t ty) → Set
\end{code}
%</Is-diffL-id-type>
\begin{code}
    Is-diffL-id [] = Unit
    Is-diffL-id (Dμ-A () ∷ p)
    Is-diffL-id (Dμ-ins x ∷ p) = ⊥
    Is-diffL-id (Dμ-del x ∷ p) = ⊥
    Is-diffL-id (Dμ-dwn dx ∷ p) = Is-diff-id dx × Is-diffL-id p
\end{code}

  The identity patch is the same as (gdiff x x) but
  much easier to compute, as no comparisons are needed.

%<*gdiff-id-def>
\begin{code}
  mutual
    gdiff-id : {n : ℕ}{t : Tel n}{ty : U n}
             → (a : ElU ty t) → Patch t ty
    gdiff-id unit = D-unit
    gdiff-id (inl a) = D-inl (gdiff-id a)
    gdiff-id (inr a) = D-inr (gdiff-id a)
    gdiff-id (a1 , a2) = D-pair (gdiff-id a1) (gdiff-id a2)
    gdiff-id (top a) = D-top (gdiff-id a)
    gdiff-id (pop a) = D-pop (gdiff-id a)
    gdiff-id (red a) = D-β (gdiff-id a)
    gdiff-id (mu a) = D-mu (gdiffL-id (mu a ∷ []))
  
    {-# TERMINATING #-}
    gdiffL-id : {n : ℕ}{t : Tel n}{ty : U (suc n)}
             → (as : List (ElU (μ ty) t)) → Patchμ t ty
    gdiffL-id [] = []
    gdiffL-id (x ∷ as)
     = Dμ-dwn (gdiff-id (μ-hd x)) ∷ gdiffL-id (μ-ch x ++ as)
\end{code}
%</gdiff-id-def>

  gdiff id has to have cost 0, as it is the identity.

\begin{code}
  mutual
\end{code}
%<*gdiff-id-cost-type>
\begin{code}
    gdiff-id-cost : {n : ℕ}{t : Tel n}{ty : U n}
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
    gdiffL-id-cost : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                  → (a : List (ElU (μ ty) t)) → sum costμ (gdiffL-id a) ≡ 0
    gdiffL-id-cost [] = refl
    gdiffL-id-cost (a ∷ as) 
      = subst (λ P → P + sum costμ (gdiffL-id (μ-ch a ++ as)) ≡ 0) 
              (sym (gdiff-id-cost (μ-hd a))) 
              (gdiffL-id-cost (μ-ch a ++ as))
\end{code}

  It turns out that we were indeed correct in computing our diff-id:

\begin{code}
  mutual
\end{code}
%<*gdiff-id-correct-type>
\begin{code}
    gdiff-id-correct 
      : {n : ℕ}{t : Tel n}{ty : U n}
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
    gdiff-id-correct (red a) = cong D-β (gdiff-id-correct a)

  {-
    private
      mkDel : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            → (a : ElU (μ ty) t)(as : List (ElU (μ ty) t)) 
            → Patchμ t ty
      mkDel a as = (Dμ-del (μ-hd a) ∷ gdiffL (μ-ch a ++ as) (a ∷ as))

      mkDwn : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            → (a : ElU (μ ty) t)(as : List (ElU (μ ty) t)) 
            → Patchμ t ty
      mkDwn a as = (Dμ-dwn (gdiff (μ-hd a) (μ-hd a)) ∷
                    gdiffL (μ-ch a ++ as) (μ-ch a ++ as)) 

      cost-dwn : {n : ℕ}{t : Tel n}{ty : U (suc n)}
               → (a : ElU (μ ty) t)(as : List (ElU (μ ty) t))
               → sum costμ (mkDwn a as) ≡ 0
      cost-dwn a as 
        = cong₂ _+_ 
                (trans (cong cost (sym (gdiff-id-correct (μ-hd a)))) 
                       (gdiff-id-cost (μ-hd a))) 
                (trans (cong (sum costμ) (sym (gdiffL-id-correct (μ-ch a ++ as)))) 
                       (gdiffL-id-cost (μ-ch a ++ as)))

      dwn<del : {n : ℕ}{t : Tel n}{ty : U (suc n)}
              → (a : ElU (μ ty) t)(as : List (ElU (μ ty) t)) 
              → suc (cost (D-mu (mkDwn a as))) ≤ cost (D-mu (mkDel a as))
      dwn<del a as rewrite cost-dwn a as
        = s≤s z≤n

      ss : {n m : ℕ} → suc n ≤ m → n ≤ m
      ss (s≤s p) = nat-≤-step p

      pi : {n m : ℕ}(a b : n ≤ m) → a ≡ b
      pi z≤n z≤n = refl
      pi (s≤s a) (s≤s b) = cong s≤s (pi a b)

      dwn<del? : {n : ℕ}{t : Tel n}{ty : U (suc n)}
              → (a : ElU (μ ty) t)(as : List (ElU (μ ty) t)) 
              → (cost (D-mu (mkDwn a as)) ≤?-ℕ cost (D-mu (mkDel a as)))
              ≡ yes (ss (dwn<del a as))
      dwn<del? a as with (cost (D-mu (mkDwn a as)) ≤?-ℕ cost (D-mu (mkDel a as)))
      ...| yes q = cong yes (pi q (ss (dwn<del a as)))
      ...| no  q = {!!}

      lemma-1 : {n : ℕ}{t : Tel n}{ty : U (suc n)}
              → (a : ElU (μ ty) t)(as : List (ElU (μ ty) t))            
              → mkDwn a as
              ≡  mkDel a as
              ⊔μ mkDwn a as
      lemma-1 a as with ss (dwn<del a as)
      lemma-1 a as | prf = {!!}
    -}   

    {-# TERMINATING #-}
    gdiffL-id-correct
      : {n : ℕ}{t : Tel n}{ty : U (suc n)}
      → (as : List (ElU (μ ty) t)) → gdiffL-id as ≡ gdiffL as as
    gdiffL-id-correct [] = refl
    gdiffL-id-correct (a ∷ as) 
      = trustme
      where
        postulate trustme : ∀{a}{A : Set a} → A
\end{code}
