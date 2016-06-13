\begin{code}
open import Prelude
open import Prelude.NatProperties
  using (+-comm)
open import Diffing.Universe
open import Diffing.Patches.D
open import Diffing.Patches.Cost
open import Diffing.Diff
open import Diffing.Apply

module Diffing.Patches.Inverse where

  open Cost {{...}}

  open import Prelude.Monad
  open Monad {{...}}
\end{code}

\begin{code}
  mutual
\end{code}
%<*D-inv-type>
\begin{code}
    D-inv : {n : ℕ}{t : T n}{ty : U n}
          → Patch t ty → Patch t ty
\end{code}
%</D-inv-type>
\begin{code}
    D-inv (D-A ())
    D-inv D-unit = D-unit
    D-inv (D-inl p) = D-inl (D-inv p)
    D-inv (D-inr p) = D-inr (D-inv p)
    D-inv (D-setl x y) = D-setr y x
    D-inv (D-setr x y) = D-setl y x
    D-inv (D-pair p q) = D-pair (D-inv p) (D-inv q)
    D-inv (D-mu x) = D-mu (Dμ-inv x)
    D-inv (D-def p) = D-def (D-inv p)
    D-inv (D-top p) = D-top (D-inv p)
    D-inv (D-pop p) = D-pop (D-inv p)
    
    {-# TERMINATING #-}
    Dμ-inv : {n : ℕ}{t : T n}{ty : U (suc n)}
           → Patchμ t ty → Patchμ t ty
    Dμ-inv = map Dμ-inv1

    Dμ-inv1 : {n : ℕ}{t : T n}{ty : U (suc n)}
            → Dμ ⊥ₚ t ty → Dμ ⊥ₚ t ty
    Dμ-inv1 (Dμ-A ())
    Dμ-inv1 (Dμ-ins x) = Dμ-del x
    Dμ-inv1 (Dμ-del x) = Dμ-ins x
    Dμ-inv1 (Dμ-dwn x) = Dμ-dwn (D-inv x)
\end{code}

\begin{code}
  mutual
\end{code}
%<*D-inv-cost-type>
\begin{code}
    D-inv-cost : {n : ℕ}{t : T n}{ty : U n}{Δ : Cost}
               → (d : Patch t ty)
               → cost Δ d ≡ cost Δ (D-inv d)
\end{code}
%</D-inv-cost-type>
\begin{code}
    D-inv-cost (D-A ())
    D-inv-cost D-unit = refl
    D-inv-cost (D-inl d) = D-inv-cost d
    D-inv-cost (D-inr d) = D-inv-cost d
    D-inv-cost {Δ = Δ} (D-setl x x₁)
      = c⊕-sym-lemma {{Δ}} x x₁
    D-inv-cost {Δ = Δ} (D-setr x x₁)
      = c⊕-sym-lemma {{Δ}} x x₁
    D-inv-cost (D-pair p q) = cong₂ _+_ (D-inv-cost p) (D-inv-cost q)
    D-inv-cost (D-mu x) = Dμ-inv-costL x
    D-inv-cost (D-def d) = D-inv-cost d
    D-inv-cost (D-top d) = D-inv-cost d
    D-inv-cost (D-pop d) = D-inv-cost d

    Dμ-inv-costL : {n : ℕ}{t : T n}{ty : U (suc n)}{Δ : Cost}
               → (d : Patchμ t ty)
               → costL Δ d ≡ costL Δ (Dμ-inv d)
    Dμ-inv-costL [] = refl
    Dμ-inv-costL (Dμ-A () ∷ d)
    Dμ-inv-costL {Δ = Δ} (Dμ-ins x ∷ d)
      = cong (_+_ (Cμ Δ x)) (Dμ-inv-costL d)
    Dμ-inv-costL {Δ = Δ} (Dμ-del x ∷ d)
      = cong (_+_ (Cμ Δ x)) (Dμ-inv-costL d)
    Dμ-inv-costL (Dμ-dwn x ∷ d)
      = cong₂ _+_ (D-inv-cost x) (Dμ-inv-costL d)

    Dμ-inv-cost : {n : ℕ}{t : T n}{ty : U (suc n)}{Δ : Cost}
                → (d : Dμ ⊥ₚ t ty)
                → costμ Δ d ≡ costμ Δ (Dμ-inv1 d)
    Dμ-inv-cost (Dμ-A ())
    Dμ-inv-cost (Dμ-ins x) = refl
    Dμ-inv-cost (Dμ-del x) = refl
    Dμ-inv-cost (Dμ-dwn x) = D-inv-cost x
\end{code}

\begin{code}
  mutual    
    {-# TERMINATING #-}
\end{code}
%<*D-inv-spec-src-type>
\begin{code}
    D-inv-src-lemma 
      : {n : ℕ}{t : T n}{ty : U n}
      → (p : Patch t ty)
      → D-src (D-inv p) ≡ D-dst p
\end{code}
%</D-inv-src-lemma-type>
%<*D-mu-inv-src-lemma-type>
\begin{code}
    Dμ-inv-src-lemma
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (ps : Patchμ t ty)
      → Dμ-src (Dμ-inv ps) ≡ Dμ-dst ps
\end{code}
%<*D-mu-inv-src-lemma-type>
\begin{code}
    D-inv-src-lemma (D-A ())
    D-inv-src-lemma D-unit = refl
    D-inv-src-lemma (D-inl p) = cong (λ P → inl <M> P) (D-inv-src-lemma p)
    D-inv-src-lemma (D-inr p) = cong (λ P → inr <M> P) (D-inv-src-lemma p)
    D-inv-src-lemma (D-setl x x₁) = refl
    D-inv-src-lemma (D-setr x x₁) = refl
    D-inv-src-lemma (D-pair p p₁)
     rewrite D-inv-src-lemma p
           | D-inv-src-lemma p₁
           = refl
    D-inv-src-lemma (D-def p)
      = cong (λ P → red <M> P) (D-inv-src-lemma p)
    D-inv-src-lemma (D-top p)
      = cong (_<M>_ top) (D-inv-src-lemma p)
    D-inv-src-lemma (D-pop p)
      = cong (_<M>_ pop) (D-inv-src-lemma p)
    D-inv-src-lemma (D-mu x)
      rewrite Dμ-inv-src-lemma x = refl
    
    Dμ-inv-src-lemma [] = refl
    Dμ-inv-src-lemma (Dμ-A () ∷ ps)
    Dμ-inv-src-lemma (Dμ-ins x ∷ ps)
      rewrite Dμ-inv-src-lemma ps = refl
    Dμ-inv-src-lemma (Dμ-del x ∷ ps)
      rewrite Dμ-inv-src-lemma ps = refl
    Dμ-inv-src-lemma (Dμ-dwn x ∷ ps)
      rewrite D-inv-src-lemma x
            | Dμ-inv-src-lemma ps = refl
\end{code}

\begin{code}
  mutual    
    {-# TERMINATING #-}
\end{code}
%<*D-inv-dst-lemma-type>
\begin{code}
    D-inv-dst-lemma 
      : {n : ℕ}{t : T n}{ty : U n}
      → (p : Patch t ty)
      → D-dst (D-inv p) ≡ D-src p
\end{code}
%</D-inv-dst-lemma-type>
%<*D-mu-inv-dst-lemma-type>
\begin{code}
    Dμ-inv-dst-lemma
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (ps : Patchμ t ty)
      → Dμ-dst (Dμ-inv ps) ≡ Dμ-src ps
\end{code}
%<*D-mu-inv-dst-lemma-type>
\begin{code}
    D-inv-dst-lemma (D-A ())
    D-inv-dst-lemma D-unit = refl
    D-inv-dst-lemma (D-inl p) = cong (λ P → inl <M> P) (D-inv-dst-lemma p)
    D-inv-dst-lemma (D-inr p) = cong (λ P → inr <M> P) (D-inv-dst-lemma p)
    D-inv-dst-lemma (D-setl x x₁) = refl
    D-inv-dst-lemma (D-setr x x₁) = refl
    D-inv-dst-lemma (D-pair p p₁)
     rewrite D-inv-dst-lemma p
           | D-inv-dst-lemma p₁
           = refl
    D-inv-dst-lemma (D-def p)
      = cong (λ P → red <M> P) (D-inv-dst-lemma p)
    D-inv-dst-lemma (D-top p)
      = cong (_<M>_ top) (D-inv-dst-lemma p)
    D-inv-dst-lemma (D-pop p)
      = cong (_<M>_ pop) (D-inv-dst-lemma p)
    D-inv-dst-lemma (D-mu x)
      rewrite Dμ-inv-dst-lemma x = refl
    
    Dμ-inv-dst-lemma [] = refl
    Dμ-inv-dst-lemma (Dμ-A () ∷ ps)
    Dμ-inv-dst-lemma (Dμ-ins x ∷ ps)
      rewrite Dμ-inv-dst-lemma ps = refl
    Dμ-inv-dst-lemma (Dμ-del x ∷ ps)
      rewrite Dμ-inv-dst-lemma ps = refl
    Dμ-inv-dst-lemma (Dμ-dwn x ∷ ps)
      rewrite D-inv-dst-lemma x
            | Dμ-inv-dst-lemma ps = refl
\end{code}
