\begin{code}
open import Prelude
open import Diffing.Universe

module Diffing.Patches.Diff.D where
\end{code}

%<*ValU>
\begin{code}
  ValU : {n : ℕ} → U (suc n) → T n → Set
  ValU ty t = ElU ty (u1 ∷ t)
\end{code}
%</ValU>

\begin{code}
  mutual
\end{code}

%<*D-type>
\begin{code}
    data D {a}(A : {n : ℕ} → T n → U n → Set a) 
      : {n : ℕ} → T n → U n → Set a where
\end{code}
%</D-type>

%<*D-A-def>
\begin{code}
      D-A    : {n : ℕ}{t : T n}{ty : U n} → A t ty → D A t ty
\end{code}
%</D-A-def>

%<*D-unit-def>
\begin{code}
      D-unit : {n : ℕ}{t : T n} → D A t u1
\end{code}
%</D-unit-def>

%<*D-sum-def>
\begin{code}
      D-inl  : {n : ℕ}{t : T n}{a b : U n} 
             → D A t a → D A t (a ⊕ b)
      D-inr  : {n : ℕ}{t : T n}{a b : U n} 
             → D A t b → D A t (a ⊕ b)
      D-setl  : {n : ℕ}{t : T n}{a b : U n} 
              → ElU a t → ElU b t → D A t (a ⊕ b)
      D-setr  : {n : ℕ}{t : T n}{a b : U n} 
              → ElU b t → ElU a t → D A t (a ⊕ b)
\end{code}
%</D-sum-def>

%<*D-pair-def>
\begin{code}
      D-pair : {n : ℕ}{t : T n}{a b : U n} 
             → D A t a → D A t b → D A t (a ⊗ b)
\end{code}
%</D-pair-def>

%<*D-mu-def>
\begin{code}
      D-mu : {n : ℕ}{t : T n}{a : U (suc n)}
           → List (Dμ A t a) → D A t (μ a)
\end{code}
%</D-mu-def>

%<*D-rest-def>
\begin{code}
      D-def : {n : ℕ}{t : T n}{F : U (suc n)}{x : U n} 
          → D A (x ∷ t) F → D A t (def F x)
      D-top : {n : ℕ}{t : T n}{a : U n}
            → D A t a → D A (a ∷ t) var
      D-pop : {n : ℕ}{t : T n}{a b : U n}
            → D A t b → D A (a ∷ t) (wk b)
\end{code}
%</D-rest-def>


%<*Dmu-type>
\begin{code}
    data Dμ {a}(A : {n : ℕ} → T n → U n → Set a) 
      : {n : ℕ} → T n → U (suc n) → Set a where
\end{code}
%</Dmu-type>

%<*Dmu-A-def>
\begin{code}
      Dμ-A   : {n : ℕ}{t : T n}{a : U (suc n)} 
             → A t (μ a) → Dμ A t a
\end{code}
%</Dmu-A-def>

%<*Dmu-def>
\begin{code}
      Dμ-ins : {n : ℕ}{t : T n}{a : U (suc n)} 
             → ValU a t → Dμ A t a
      Dμ-del : {n : ℕ}{t : T n}{a : U (suc n)} 
             → ValU a t → Dμ A t a
      Dμ-dwn : {n : ℕ}{t : T n}{a : U (suc n)} 
             → D A (u1 ∷ t) a → Dμ A t a
\end{code}
%</Dmu-def>

%<*Patch-def>
\begin{code}
  ⊥ₚ : {n : ℕ} → T n → U n → Set
  ⊥ₚ {_} _ _ = ⊥

  Patch : {n : ℕ} → T n → U n → Set
  Patch t ty = D ⊥ₚ t ty
       
  Patchμ : {n : ℕ} → T n → U (suc n) → Set
  Patchμ t ty = List (Dμ ⊥ₚ t ty)
\end{code}
%</Patch-def>
