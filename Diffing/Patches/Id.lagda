\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Universe.Measures
open import Diffing.Patches.Diff

module Diffing.Patches.Id where
\end{code}

  It is easy to check whether a diff is the identity
  diff of a given element or not. 
  This is a simple decidable property

%<*Is-diff-id-def>
\begin{code}
  mutual
    Is-diff-id : {n : ℕ}{t : Tel n}{ty : U n}
               → (d : Patch t ty) → Set
    Is-diff-id (D-A ())
    Is-diff-id D-void = Unit
    Is-diff-id (D-inl p) = Is-diff-id p
    Is-diff-id (D-inr p) = Is-diff-id p
    Is-diff-id (D-setl x x₁) = ⊥
    Is-diff-id (D-setr x x₁) = ⊥
    Is-diff-id (D-pair p q) = Is-diff-id p × Is-diff-id q
    Is-diff-id (D-mu x) = Is-diffL-id x × (x ≡ [] → ⊥)
    Is-diff-id (D-β p) = Is-diff-id p
    Is-diff-id (D-top p) = Is-diff-id p
    Is-diff-id (D-pop p) = Is-diff-id p

    Is-diffL-id : {n : ℕ}{t : Tel n}{ty : U (suc n)}
               → (d : Patchμ t ty) → Set
    Is-diffL-id [] = Unit
    Is-diffL-id (Dμ-A () ∷ p)
    Is-diffL-id (Dμ-ins x ∷ p) = ⊥
    Is-diffL-id (Dμ-del x ∷ p) = ⊥
    Is-diffL-id (Dμ-cpy x ∷ p) = Is-diffL-id p
    Is-diffL-id (Dμ-dwn dx ∷ p) = Is-diff-id dx × Is-diffL-id p
\end{code}
%</Is-diff-id-def>

  The identity patch is the same as (gdiff x x) but
  much easier to compute, as no comparisons are needed.

%<*gdiff-id-def>
\begin{code}
  mutual
    gdiff-id : {n : ℕ}{t : Tel n}{ty : U n}
             → (a : ElU ty t) → Patch t ty
    gdiff-id void = D-void
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
    gdiffL-id (x ∷ as) with μ-open x
    ...| hdX , chX = Dμ-cpy hdX ∷ gdiffL-id (chX ++ as)
\end{code}
%</gdiff-id-def>

  It turns out that we were indeed correct in computing our diff-id:

%<*gdiff-id-correct>
\begin{code}
  mutual
    gdiff-id-correct 
      : {n : ℕ}{t : Tel n}{ty : U n}
      → (a : ElU ty t) → gdiff-id a ≡ gdiff a a
    gdiff-id-correct void = refl
    gdiff-id-correct (inl a) = cong D-inl (gdiff-id-correct a)
    gdiff-id-correct (inr a) = cong D-inr (gdiff-id-correct a)
    gdiff-id-correct (a1 , a2) 
      = cong₂ D-pair (gdiff-id-correct a1) (gdiff-id-correct a2)
    gdiff-id-correct (top a) = cong D-top (gdiff-id-correct a)
    gdiff-id-correct (pop a) = cong D-pop (gdiff-id-correct a)
    gdiff-id-correct (mu a) = cong D-mu (gdiffL-id-correct (mu a ∷ []))
    gdiff-id-correct (red a) = cong D-β (gdiff-id-correct a)

    {-# TERMINATING #-}
    gdiffL-id-correct
      : {n : ℕ}{t : Tel n}{ty : U (suc n)}
      → (as : List (ElU (μ ty) t)) → gdiffL-id as ≡ gdiffL as as
    gdiffL-id-correct [] = refl
    gdiffL-id-correct (a ∷ as) with μ-open a
    ...| hdA , chA rewrite ≟-U-refl hdA 
       = cong (_∷_ (Dμ-cpy hdA)) (gdiffL-id-correct (chA ++ as))      
\end{code}
%</gdiff-id-correct>

  Now, it is important that Is-diff-id is correct and sound!

%<Is-diff-id-sound>
begin{code}
  mutual
    diff-id-sound : {n : ℕ}{t : Tel n}{ty : U n}
                  → (p : Patch t ty)
                  → Is-diff-id p
                  → ∃ (λ el → p ≡ gdiff-id el)
    diff-id-sound (D-A ()) prf
    diff-id-sound D-void prf = void , refl
    diff-id-sound (D-inl p) prf 
      = split (inl ∘ p1) (cong D-inl ∘ p2) (diff-id-sound p prf)
    diff-id-sound (D-inr p) prf 
      = split (inr ∘ p1) (cong D-inr ∘ p2) (diff-id-sound p prf)
    diff-id-sound (D-setl x x₁) ()
    diff-id-sound (D-setr x x₁) ()
    diff-id-sound (D-pair p q) (pp , pq) 
      = let (ep , hipP) = diff-id-sound p pp
      in split (_,_ ep ∘ p1) (cong₂ D-pair hipP ∘ p2) (diff-id-sound q pq)
    diff-id-sound (D-mu x) (prf , abs) 
      = split (mu ∘ p1) (cong D-mu ∘ p2) {! (diffL-id-sound x prf abs) !}
    diff-id-sound (D-β p) prf = {!!}
    diff-id-sound (D-top p) prf = {!!}
    diff-id-sound (D-pop p) prf = {!!}

    diffL-id-sound : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                   → (p : Patchμ t ty)
                   → Is-diffL-id p
                   → (p ≡ [] → ⊥)
                   → ∃ (λ el → p ≡ gdiffL-id (el ∷ [])) 
    diffL-id-sound [] prf abs = ⊥-elim (abs refl)
    diffL-id-sound (Dμ-A () ∷ p) prf abs
    diffL-id-sound (Dμ-ins x ∷ p) () abs
    diffL-id-sound (Dμ-del x ∷ p) () abs
    diffL-id-sound (Dμ-cpy x ∷ p) prf abs = {!!}
    diffL-id-sound (Dμ-dwn dx ∷ p) (dxId , pId) abs = {!!}
end{code}
%</Is-diff-id-sound>
