\begin{code}
open import Prelude
open import Prelude.Vector
open import Prelude.ListProperties using (All; all?)

open import Prelude.Monad
open import Diffing.CF-base

module Diffing.Patches.D where
\end{code}

  Here we define our Patch datatype and
  both projections: source and destination.

%<*natural-transformation-def>
\begin{code}
  open Monad {{...}}

  infixr 3 _⇒_

  _⇒_ : (A : {n : ℕ} → U n → T n → Set)
      → (B : {n : ℕ} → U n → T n → Set)
      → Set
  A ⇒ B = {n : ℕ}{t : T n}{ty : U n} → A ty t → B ty t
\end{code}
%</natural-transformation-def>

\begin{code}
  mutual
\end{code}
%<*D-type>
\begin{code}
    data D (A : {n : ℕ} → U n → T n → Set) 
      : {n : ℕ} → U n → T n → Set where
\end{code}
%</D-type>
%<*D-A-def>
\begin{code}
      D-A    : {n : ℕ}{t : T n}{ty : U n} → A ty t → D A ty t
\end{code}
%</D-A-def>
%<*D-void-def>
\begin{code}
      D-unit : {n : ℕ}{t : T n} → D A u1 t
\end{code}
%</D-void-def>
%<*D-sum-def>
\begin{code}
      D-inl  : {n : ℕ}{t : T n}{a b : U n} 
             → D A a t → D A (a ⊕ b) t
      D-inr  : {n : ℕ}{t : T n}{a b : U n} 
             → D A b t → D A (a ⊕ b) t
      D-setl : {n : ℕ}{t : T n}{a b : U n} 
             → ElU a t → ElU b t → D A (a ⊕ b) t
      D-setr : {n : ℕ}{t : T n}{a b : U n} 
             → ElU b t → ElU a t → D A (a ⊕ b) t
\end{code}
%</D-sum-def>
%<*D-pair-def>
\begin{code}
      D-pair : {n : ℕ}{t : T n}{a b : U n} 
             → D A a t → D A b t → D A (a ⊗ b) t
\end{code}
%</D-pair-def>
%<*D-mu-A-def>
\begin{code}
      D-μ-A : {n : ℕ}{t : T n}{a : U (suc n)}
            → A (μ a) t → D A (μ a) t → D A (μ a) t 
\end{code}
%</D-mu-A-def>
%<*D-mu-dwn-def>
\begin{code}
      D-μ-dwn : {n : ℕ}{t : T n}{a : U (suc n)}
              → (d : D A a (u1 ∷ t))
              → List (D A (μ a) t) → D A (μ a) t
\end{code}
%</D-mu-dwn-def>
%<*D-mu-add-rmv-def>
\begin{code}
      D-μ-add : {n : ℕ}{t : T n}{a : U (suc n)}
              → Ctx 0 a (μ a ∷ t) → D A (μ a) t → D A (μ a) t
      D-μ-rmv : {n : ℕ}{t : T n}{a : U (suc n)}
              → Ctx 0 a (μ a ∷ t) → D A (μ a) t → D A (μ a) t
\end{code}
%</D-mu-add-rmv-def>
%<*D-rest-def>
\begin{code}
      D-def : {n : ℕ}{t : T n}{F : U (suc n)}{x : U n} 
            → D A F (x ∷ t) → D A (def F x) t
      D-top : {n : ℕ}{t : T n}{a : U n}
            → D A a t → D A var (a ∷ t)
      D-pop : {n : ℕ}{t : T n}{a b : U n}
            → D A b t → D A (wk b) (a ∷ t) 
\end{code}
%</D-rest-def>

\begin{code}
    {-# TERMINATING #-}
    D-arᵢ D-arₒ
      : {A : {n : ℕ} → U n → T n → Set}
        {n : ℕ}{t : T n}{ty : U n}
      → ℕ → D A ty t → ℕ
\end{code}
\begin{code}
    D-arᵢ i (D-A x) = 0
    D-arᵢ i (D-μ-A x p) = D-arᵢ i p
    D-arᵢ i D-unit = 0
    D-arᵢ i (D-inl d) = D-arᵢ i d
    D-arᵢ i (D-inr d) = D-arᵢ i d
    D-arᵢ i (D-setl x y) = ar i x
    D-arᵢ i (D-setr x y) = ar i x
    D-arᵢ i (D-pair d p) = D-arᵢ i d + D-arᵢ i p
    D-arᵢ i (D-def d) = D-arᵢ (suc i) d
    D-arᵢ zero    (D-top d) = 1
    D-arᵢ (suc i) (D-top d) = D-arᵢ i d
    D-arᵢ zero    (D-pop d) = 0
    D-arᵢ (suc i) (D-pop d) = D-arᵢ i d
    D-arᵢ i (D-μ-dwn d ps)
      = D-arᵢ (suc i) d + sum (map (D-arᵢ i) ps)
    D-arᵢ i (D-μ-add x d)
      = D-arᵢ i d
    D-arᵢ i (D-μ-rmv x d)
      = φ-ar (suc i) x + D-arᵢ i d

    D-arₒ i (D-A x) = 0
    D-arₒ i (D-μ-A x p) = D-arₒ i p
    D-arₒ i D-unit = 0
    D-arₒ i (D-inl d) = D-arₒ i d
    D-arₒ i (D-inr d) = D-arₒ i d
    D-arₒ i (D-setl x y) = ar i y
    D-arₒ i (D-setr x y) = ar i y
    D-arₒ i (D-pair d p) = D-arₒ i d + D-arₒ i p 
    D-arₒ i (D-def d) = D-arₒ (suc i) d
    D-arₒ zero (D-top d) = 1
    D-arₒ (suc i) (D-top d) = D-arₒ i d
    D-arₒ zero (D-pop d) = 0
    D-arₒ (suc i) (D-pop d) = D-arₒ i d
    D-arₒ i (D-μ-dwn d ps)
      = D-arₒ (suc i) d + sum (map (D-arₒ i) ps)
    D-arₒ i (D-μ-add x d)
      = φ-ar (suc i) x + D-arₒ i d
    D-arₒ i (D-μ-rmv x d)
      = D-arₒ i d
\end{code}

%<*Patch-def>
\begin{code}
  ⊥ₚ : {n : ℕ} → U n → T n → Set
  ⊥ₚ {_} _ _ = ⊥

  Patch : {n : ℕ} → U n → T n → Set
  Patch ty t = D ⊥ₚ ty t
\end{code}
%</Patch-def>

%<*D-src-type>
\begin{code}
  {-# TERMINATING #-}
  D-src : {n : ℕ}{t : T n}{ty : U n}
        → Patch ty t → Maybe (ElU ty t)
\end{code}
%</D-src-type>
%<*D-src-def>
\begin{code}
  D-src (D-A ())
  D-src (D-μ-A () _)
  D-src D-unit = just unit
  D-src (D-inl d) = inl <M> D-src d
  D-src (D-inr d) = inr <M> D-src d
  D-src (D-setl x _) = just (inl x)
  D-src (D-setr x _) = just (inr x)
  D-src (D-pair d e) = _,_ <M> (D-src d) <M*> (D-src e)
  D-src (D-def d) = red <M> D-src d
  D-src (D-top d) = top <M> D-src d
  D-src (D-pop d) = pop <M> D-src d
  D-src (D-μ-dwn dx d)
    = mu <M> join (plug 0 <M> D-src dx <M*> mapM (λ x → pop <M> D-src x) d)
  D-src (D-μ-add ctx d)
    = D-src d
  D-src (D-μ-rmv ctx d)
    = (mu ∘ _◂_ ctx ∘ pop) <M> (D-src d)
\end{code}
%</D-src-def>


%<*D-dst-type>
\begin{code}
  {-# TERMINATING #-}
  D-dst : {n : ℕ}{t : T n}{ty : U n}
        → Patch ty t → Maybe (ElU ty t)
\end{code}
%</D-dst-type>
%<*D-dst-def>
\begin{code}
  D-dst (D-A ())
  D-dst (D-μ-A () _)
  D-dst D-unit = just unit
  D-dst (D-inl d) = inl <M> D-dst d
  D-dst (D-inr d) = inr <M> D-dst d
  D-dst (D-setl _ x) = just (inr x)
  D-dst (D-setr _ x) = just (inl x)
  D-dst (D-pair d e) = _,_ <M> D-dst d <M*> D-dst e
  D-dst (D-def d) = red <M> (D-dst d)
  D-dst (D-top d) = top <M> (D-dst d)
  D-dst (D-pop d) = pop <M> (D-dst d)
  D-dst (D-μ-dwn dx d)
    = mu <M> join (plug 0 <M> D-dst dx <M*> mapM (λ x → pop <M> D-dst x) d)
  D-dst (D-μ-rmv ctx d)
    = D-dst d
  D-dst (D-μ-add ctx d)
    = (mu ∘ _◂_ ctx ∘ pop) <M> D-dst d
\end{code}
%</D-dst-def>

\begin{code}
  [_,_]⇒_ : {n : ℕ}{t : T n}{ty : U n}
          → (x y : ElU ty t)(p : Patch ty t)
          → Set
  [ x , y ]⇒ p = D-src p ≡ just x × D-dst p ≡ just y
\end{code}

\begin{code}
  {-# TERMINATING #-}
  D-is-id : {n : ℕ}{t : T n}{ty : U n}
          → Patch ty t → Set
  D-is-id (D-A ())
  D-is-id (D-μ-A () _)
  D-is-id D-unit = Unit
  D-is-id (D-inl p) = D-is-id p
  D-is-id (D-inr p) = D-is-id p
  D-is-id (D-setl x x₁) = ⊥
  D-is-id (D-setr x x₁) = ⊥
  D-is-id (D-pair p q) = D-is-id p × D-is-id q
  D-is-id (D-μ-dwn p ps) = D-is-id p × All D-is-id ps
  D-is-id (D-μ-add x p) = ⊥
  D-is-id (D-μ-rmv x p) = ⊥
  D-is-id (D-def p) = D-is-id p
  D-is-id (D-top p) = D-is-id p
  D-is-id (D-pop p) = D-is-id p
\end{code}

\begin{code}
  {-# TERMINATING #-}
  D-is-id? : {n : ℕ}{t : T n}{ty : U n}
           → (p : Patch ty t) → Dec (D-is-id p)
  D-is-id? (D-A ())
  D-is-id? (D-μ-A () _)
  D-is-id? D-unit = yes unit
  D-is-id? (D-inl p) = D-is-id? p
  D-is-id? (D-inr p) = D-is-id? p
  D-is-id? (D-setl x x₁) = no (λ z → z)
  D-is-id? (D-setr x x₁) = no (λ z → z)
  D-is-id? (D-pair p q) 
    with D-is-id? p | D-is-id? q
  ...| yes pp | yes qq = yes (pp , qq)
  ...| yes pp | no  qq = no (qq ∘ p2)
  ...| no  pp | _      = no (pp ∘ p1)
  D-is-id? (D-μ-dwn px ps)
    with D-is-id? px | all? D-is-id? ps
  ...| yes ppx | yes allps = yes (ppx , allps)
  ...| yes ppx | no  allps = no (allps ∘ p2)
  ...| no  ppx | _         = no (ppx ∘ p1)
  D-is-id? (D-μ-add x p) = no (λ z → z)
  D-is-id? (D-μ-rmv x p) = no (λ z → z)
  D-is-id? (D-def p) = D-is-id? p
  D-is-id? (D-top p) = D-is-id? p
  D-is-id? (D-pop p) = D-is-id? p
\end{code}

\begin{code}
  {-# TERMINATING #-}
  gdiff-id : {n : ℕ}{t : T n}{ty : U n}{A : {k : ℕ} → U k → T k → Set}
           → ElU ty t → D A ty t
  gdiff-id unit = D-unit
  gdiff-id (inl x) = D-inl (gdiff-id x)
  gdiff-id (inr x) = D-inr (gdiff-id x)
  gdiff-id (x , x₁) = D-pair (gdiff-id x) (gdiff-id x₁)
  gdiff-id (top x) = D-top (gdiff-id x)
  gdiff-id (pop x) = D-pop (gdiff-id x)
  gdiff-id (mu x) = D-μ-dwn (gdiff-id (fgt 0 x)) (map (gdiff-id ∘ unpop) (ch 0 x))
  gdiff-id (red x) = D-def (gdiff-id x)
\end{code}
