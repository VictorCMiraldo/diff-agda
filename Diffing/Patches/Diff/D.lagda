\begin{code}
open import Prelude
open import Diffing.Universe.Syntax

module Diffing.Patches.Diff.D where
\end{code}


%<*ValU>
\begin{code}
  ValU : {n : ℕ} → U (suc n) → Tel n → Set
  ValU ty t = ElU ty (tcons u1 t)
\end{code}
%</ValU>

\begin{code}
  mutual
\end{code}

%<*D-type>
\begin{code}
    data D {a}(A : {n : ℕ} → Tel n → U n → Set a) 
      : {n : ℕ} → Tel n → U n → Set a where
\end{code}
%</D-type>

%<*D-A-def>
\begin{code}
      D-A    : {n : ℕ}{t : Tel n}{ty : U n} → A t ty → D A t ty
\end{code}
%</D-A-def>

%<*D-void-def>
\begin{code}
      D-void : {n : ℕ}{t : Tel n} → D A t u1
\end{code}
%</D-void-def>

%<*D-sum-def>
\begin{code}
      D-inl  : {n : ℕ}{t : Tel n}{a b : U n} 
             → D A t a → D A t (a ⊕ b)
      D-inr  : {n : ℕ}{t : Tel n}{a b : U n} 
             → D A t b → D A t (a ⊕ b)
      D-setl  : {n : ℕ}{t : Tel n}{a b : U n} 
              → ElU a t → ElU b t → D A t (a ⊕ b)
      D-setr  : {n : ℕ}{t : Tel n}{a b : U n} 
              → ElU b t → ElU a t → D A t (a ⊕ b)
\end{code}
%</D-sum-def>

%<*D-pair-def>
\begin{code}
      D-pair : {n : ℕ}{t : Tel n}{a b : U n} 
             → D A t a → D A t b → D A t (a ⊗ b)
\end{code}
%</D-pair-def>

%<*D-mu-def>
\begin{code}
      D-mu : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → List (Dμ A t a) → D A t (μ a)
\end{code}
%</D-mu-def>

%<*D-rest-def>
\begin{code}
      D-β : {n : ℕ}{t : Tel n}{F : U (suc n)}{x : U n} 
          → D A (tcons x t) F → D A t (β F x)
      D-top : {n : ℕ}{t : Tel n}{a : U n}
            → D A t a → D A (tcons a t) vl
      D-pop : {n : ℕ}{t : Tel n}{a b : U n}
            → D A t b → D A (tcons a t) (wk b)
\end{code}
%</D-rest-def>


%<*Dmu-type>
\begin{code}
    data Dμ {a}(A : {n : ℕ} → Tel n → U n → Set a) 
      : {n : ℕ} → Tel n → U (suc n) → Set a where
\end{code}
%</Dmu-type>

%<*Dmu-A-def>
\begin{code}
      Dμ-A   : {n : ℕ}{t : Tel n}{a : U (suc n)} 
             → A t (μ a) → Dμ A t a
\end{code}
%</Dmu-A-def>

%<*Dmu-def>
\begin{code}
      Dμ-ins : {n : ℕ}{t : Tel n}{a : U (suc n)} 
             → ValU a t → Dμ A t a
      Dμ-del : {n : ℕ}{t : Tel n}{a : U (suc n)} 
             → ValU a t → Dμ A t a
      Dμ-cpy : {n : ℕ}{t : Tel n}{a : U (suc n)} 
             → ValU a t → Dμ A t a
      Dμ-dwn : {n : ℕ}{t : Tel n}{a : U (suc n)} 
             → D A t (β a u1) → Dμ A t a
\end{code}
%</Dmu-def>

%<*Patch-def>
\begin{code}
  ⊥ₚ : {n : ℕ} → Tel n → U n → Set
  ⊥ₚ {_} _ _ = ⊥

  Patch : {n : ℕ} → Tel n → U n → Set
  Patch t ty = D ⊥ₚ t ty
       
  Patchμ : {n : ℕ} → Tel n → U (suc n) → Set
  Patchμ t ty = List (Dμ ⊥ₚ t ty)
\end{code}
%</Patch-def>
