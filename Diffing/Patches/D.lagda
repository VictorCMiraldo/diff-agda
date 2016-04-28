\begin{code}
open import Prelude
open import Prelude.Vector
open import CF
open import CF.Derivative

module Diffing.Patches.D where
\end{code}

  Here we define our Patch datatype and
  both projections: source and destination.

%<*D-type>
\begin{code}
  data D {a}(A : {n : ℕ} → U n → T n → Set a) 
    : {n : ℕ} → U n → T n → Set a where
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

  For D-μ-dwn, we are already taking advantage of
  the isomorphism between A² and Patch A. 

%<*D-mu-dwn-def>
\begin{code}
    D-μ-dwn : {n : ℕ}{t : T n}{a : U (suc n)}
            → (x y : ElU a (u1 ∷ t))(hip : ar 0 x ≡ ar 0 y)
            → Vec (D A (μ a) t) (ar 0 x) → D A (μ a) t
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

%<*natural-transformation-def>
\begin{code}
  infixr 3 _⇒_

  _⇒_ : (A : {n : ℕ} → U n → T n → Set)
      → (B : {n : ℕ} → U n → T n → Set)
      → Set
  A ⇒ B = {n : ℕ}{t : T n}{ty : U n} → A ty t → B ty t
\end{code}
%</natural-transformation-def>

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
  D-src : Patch ⇒ ElU
\end{code}
%</D-src-type>
%<*D-src-def>
\begin{code}
  D-src (D-A ())
  D-src D-unit = unit
  D-src (D-inl d) = inl (D-src d)
  D-src (D-inr d) = inr (D-src d)
  D-src (D-setl x _) = inl x
  D-src (D-setr x _) = inr x
  D-src (D-pair d e) = D-src d , D-src e
  D-src (D-def d) = red (D-src d)
  D-src (D-top d) = top (D-src d)
  D-src (D-pop d) = pop (D-src d)
  D-src (D-μ-dwn x y hip d)
    = mu (plugv 0 x (vmap (pop ∘ D-src) d))
  D-src (D-μ-add ctx d)
    = D-src d
  D-src (D-μ-rmv ctx d)
    = mu (ctx ◂ pop (D-src d))
\end{code}
%</D-src-def>

%<*D-dst-type>
\begin{code}
  {-# TERMINATING #-}
  D-dst : Patch ⇒ ElU
\end{code}
%</D-dst-type>
%<*D-dst-def>
\begin{code}
  D-dst (D-A ())
  D-dst D-unit = unit
  D-dst (D-inl d) = inl (D-dst d)
  D-dst (D-inr d) = inr (D-dst d)
  D-dst (D-setl _ x) = inr x
  D-dst (D-setr _ x) = inl x
  D-dst (D-pair d e) = D-dst d , D-dst e
  D-dst (D-def d) = red (D-dst d)
  D-dst (D-top d) = top (D-dst d)
  D-dst (D-pop d) = pop (D-dst d)
  D-dst (D-μ-dwn x y hip d) rewrite hip
    = mu (plugv 0 y (vmap (pop ∘ D-dst) d))
  D-dst (D-μ-rmv ctx d)
    = D-dst d
  D-dst (D-μ-add ctx d)
    = mu (ctx ◂ pop (D-dst d))
\end{code}
%</D-dst-def>
