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
    D-inv-spec-src 
      : {n : ℕ}{t : T n}{ty : U n}
      → (p : Patch t ty)
      → D-src (D-inv p) ≡ D-dst p
\end{code}
%</D-inv-spec-src-type>
%<*D-mu-inv-spec-src-type>
\begin{code}
    Dμ-inv-spec-src
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (ps : Patchμ t ty)
      → Dμ-src (Dμ-inv ps) ≡ Dμ-dst ps
\end{code}
%<*D-mu-inv-spec-src-type>
\begin{code}
    D-inv-spec-src (D-A ())
    D-inv-spec-src D-unit = refl
    D-inv-spec-src (D-inl p) = cong (λ P → inl <M> P) (D-inv-spec-src p)
    D-inv-spec-src (D-inr p) = cong (λ P → inr <M> P) (D-inv-spec-src p)
    D-inv-spec-src (D-setl x x₁) = refl
    D-inv-spec-src (D-setr x x₁) = refl
    D-inv-spec-src (D-pair p p₁)
     rewrite D-inv-spec-src p
           | D-inv-spec-src p₁
           = refl
    D-inv-spec-src (D-def p)
      = cong (λ P → red <M> P) (D-inv-spec-src p)
    D-inv-spec-src (D-top p)
      = cong (_<M>_ top) (D-inv-spec-src p)
    D-inv-spec-src (D-pop p)
      = cong (_<M>_ pop) (D-inv-spec-src p)
    D-inv-spec-src (D-mu x)
      rewrite Dμ-inv-spec-src x = refl
    
    Dμ-inv-spec-src [] = refl
    Dμ-inv-spec-src (Dμ-A () ∷ ps)
    Dμ-inv-spec-src (Dμ-ins x ∷ ps)
      rewrite Dμ-inv-spec-src ps = refl
    Dμ-inv-spec-src (Dμ-del x ∷ ps)
      rewrite Dμ-inv-spec-src ps = refl
    Dμ-inv-spec-src (Dμ-dwn x ∷ ps)
      rewrite D-inv-spec-src x
            | Dμ-inv-spec-src ps = refl
\end{code}

\begin{code}
  mutual    
    {-# TERMINATING #-}
\end{code}
%<*D-inv-spec-dst-type>
\begin{code}
    D-inv-spec-dst 
      : {n : ℕ}{t : T n}{ty : U n}
      → (p : Patch t ty)
      → D-dst (D-inv p) ≡ D-src p
\end{code}
%</D-inv-spec-dst-type>
%<*D-mu-inv-spec-dst-type>
\begin{code}
    Dμ-inv-spec-dst
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (ps : Patchμ t ty)
      → Dμ-dst (Dμ-inv ps) ≡ Dμ-src ps
\end{code}
%<*D-mu-inv-spec-dst-type>
\begin{code}
    D-inv-spec-dst (D-A ())
    D-inv-spec-dst D-unit = refl
    D-inv-spec-dst (D-inl p) = cong (λ P → inl <M> P) (D-inv-spec-dst p)
    D-inv-spec-dst (D-inr p) = cong (λ P → inr <M> P) (D-inv-spec-dst p)
    D-inv-spec-dst (D-setl x x₁) = refl
    D-inv-spec-dst (D-setr x x₁) = refl
    D-inv-spec-dst (D-pair p p₁)
     rewrite D-inv-spec-dst p
           | D-inv-spec-dst p₁
           = refl
    D-inv-spec-dst (D-def p)
      = cong (λ P → red <M> P) (D-inv-spec-dst p)
    D-inv-spec-dst (D-top p)
      = cong (_<M>_ top) (D-inv-spec-dst p)
    D-inv-spec-dst (D-pop p)
      = cong (_<M>_ pop) (D-inv-spec-dst p)
    D-inv-spec-dst (D-mu x)
      rewrite Dμ-inv-spec-dst x = refl
    
    Dμ-inv-spec-dst [] = refl
    Dμ-inv-spec-dst (Dμ-A () ∷ ps)
    Dμ-inv-spec-dst (Dμ-ins x ∷ ps)
      rewrite Dμ-inv-spec-dst ps = refl
    Dμ-inv-spec-dst (Dμ-del x ∷ ps)
      rewrite Dμ-inv-spec-dst ps = refl
    Dμ-inv-spec-dst (Dμ-dwn x ∷ ps)
      rewrite D-inv-spec-dst x
            | Dμ-inv-spec-dst ps = refl
\end{code}
