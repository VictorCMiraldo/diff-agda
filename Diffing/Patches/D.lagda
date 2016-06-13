\begin{code}
open import Prelude
open import Prelude.Monad
open import Diffing.Universe

module Diffing.Patches.D where

  open Monad {{...}}
\end{code}

%<*ValU>
\begin{code}
  ValU : {n : ℕ} → U (suc n) → T n → Set
  ValU ty t = ElU ty (u1 ∷ t)
\end{code}
%</ValU>

\begin{code}
  TU→Set : Set₁
  TU→Set = {k : ℕ} → T k → U k → Set
\end{code}

\begin{code}
  mutual
\end{code}

%<*D-type>
\begin{code}
    data D (A : TU→Set) : {n : ℕ} → T n → U n → Set where
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
    data Dμ (A : TU→Set) : {n : ℕ} → T n → U (suc n) → Set where
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

\begin{code}
  mutual
\end{code}
%<*D-src-type>
\begin{code}
    D-src : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
          → D A t ty → Maybe (ElU ty t)
\end{code}
%</D-src-type>
%<*Dmu-src-type>
\begin{code}
    Dμ-src : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
          → List (Dμ A t ty) → Maybe (List (ElU (μ ty) t))
\end{code}
%</Dmu-src-type>
%<*D-src-def>
\begin{code}
    D-src (D-A x) = nothing
    D-src D-unit = just unit
    D-src (D-inl p) = inl <M> D-src p
    D-src (D-inr p) = inr <M> D-src p
    D-src (D-setl x x₁) = just (inl x)
    D-src (D-setr x x₁) = just (inr x)
    D-src (D-pair p p₁) = _,_ <M> D-src p <M*> D-src p₁
    D-src (D-mu x) = Dμ-src x >>= lhead
    D-src (D-def p) = red <M> D-src p
    D-src (D-top p) = top <M> D-src p
    D-src (D-pop p) = pop <M> D-src p
\end{code}
%</D-src-def>
%<*Dmu-src-def>
\begin{code}
    Dμ-src [] = just []
    Dμ-src (Dμ-A x ∷ p) = nothing
    Dμ-src (Dμ-ins x ∷ p) = Dμ-src p
    Dμ-src (Dμ-del x ∷ p) = Dμ-src p >>= μ-close x >>= (return ∘ cons)
    Dμ-src (Dμ-dwn x ∷ p) = D-src x >>= (λ hdX → Dμ-src p >>= μ-close hdX >>= (return ∘ cons))
\end{code}
%</Dmu-src-def>

\begin{code}
  mutual
\end{code}
%<*D-dst-type>
\begin{code}
    D-dst : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
          → D A t ty → Maybe (ElU ty t)
\end{code}
%</D-dst-type>
%<*Dmu-dst-type>
\begin{code}
    Dμ-dst : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
          → List (Dμ A t ty) → Maybe (List (ElU (μ ty) t))
\end{code}
%</Dmu-dst-type>
%<*D-dst-def>
\begin{code}
    D-dst (D-A x) = nothing
    D-dst D-unit = just unit
    D-dst (D-inl p) = inl <M> D-dst p
    D-dst (D-inr p) = inr <M> D-dst p
    D-dst (D-setl x x₁) = just (inr x₁)
    D-dst (D-setr x x₁) = just (inl x₁)
    D-dst (D-pair p p₁) = _,_ <M> D-dst p <M*> D-dst p₁
    D-dst (D-mu x) = Dμ-dst x >>= lhead
    D-dst (D-def p) = red <M> D-dst p
    D-dst (D-top p) = top <M> D-dst p
    D-dst (D-pop p) = pop <M> D-dst p
\end{code}
%</D-dst-def>
%<*Dmu-dst-def>
\begin{code}
    Dμ-dst [] = just []
    Dμ-dst (Dμ-A x ∷ p) = nothing
    Dμ-dst (Dμ-del x ∷ p) = Dμ-dst p
    Dμ-dst (Dμ-ins x ∷ p) = Dμ-dst p >>= μ-close x >>= (return ∘ cons)
    Dμ-dst (Dμ-dwn x ∷ p) = D-dst x >>= (λ hdX → Dμ-dst p >>= μ-close hdX >>= (return ∘ cons))
\end{code}
%</Dmu-dst-def>

  And now, we define a notion
  of patch-equality.

%<*D-eq-def>
\begin{code}
  _≡-D_ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
        → (p q : D A t ty) → Set
  p ≡-D q = D-src p ≡ D-src q × D-dst p ≡ D-dst q
\end{code}
%</D-eq-def>

%<*Dmu-eq-def>
\begin{code}
  _≡-Dμ_ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
        → (p q : List (Dμ A t ty)) → Set
  p ≡-Dμ q = Dμ-src p ≡ Dμ-src q × Dμ-dst p ≡ Dμ-dst q
\end{code}
%</Dmu-eq-def>

  Of course, both relations make an equivalence
  relation over patches.

%<*D-eq-refl-type>
\begin{code}
  ≡-D-refl : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
           → (p : D A t ty)
           → p ≡-D p
\end{code}
%</D-eq-refl-type>
%<*D-eq-refl-def>
\begin{code}
  ≡-D-refl p = refl , refl
\end{code}
%</D-eq-refl-def>

%<*D-eq-sym-type>
\begin{code}
  ≡-D-sym : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
           → (p q : D A t ty)
           → p ≡-D q
           → q ≡-D p
\end{code}
%</D-eq-sym-type>
%<*D-eq-sym-def>
\begin{code}
  ≡-D-sym p q (hs , hd) = sym hs , sym hd
\end{code}
%</D-eq-sym-def>

%<*D-eq-trans-type>
\begin{code}
  ≡-D-trans : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
           → (p q r : D A t ty)
           → p ≡-D q
           → q ≡-D r
           → p ≡-D r
\end{code}
%</D-eq-trans-type>
%<*D-eq-trans-def>
\begin{code}
  ≡-D-trans p q r (hs0 , hd0) (hs1 , hd1)
    = trans hs0 hs1 , trans hd0 hd1
\end{code}
%</D-eq-trans-def>

%<*Dmu-eq-refl-type>
\begin{code}
  ≡-Dμ-refl : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
           → (p : List (Dμ A t ty))
           → p ≡-Dμ p
\end{code}
%</Dmu-eq-refl-type>
%<*Dmu-eq-refl-def>
\begin{code}
  ≡-Dμ-refl p = refl , refl
\end{code}
%</Dmu-eq-refl-def>

%<*Dmu-eq-sym-type>
\begin{code}
  ≡-Dμ-sym : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
           → (p q : List (Dμ A t ty))
           → p ≡-Dμ q
           → q ≡-Dμ p
\end{code}
%</Dmu-eq-sym-type>
%<*Dmu-eq-sym-def>
\begin{code}
  ≡-Dμ-sym p q (hs , hd) = sym hs , sym hd
\end{code}
%</Dmu-eq-sym-def>

%<*Dmu-eq-trans-type>
\begin{code}
  ≡-Dμ-trans : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
           → (p q r : List (Dμ A t ty))
           → p ≡-Dμ q
           → q ≡-Dμ r
           → p ≡-Dμ r
\end{code}
%</Dmu-eq-trans-type>
%<*Dmu-eq-trans-def>
\begin{code}
  ≡-Dμ-trans p q r (hs0 , hd0) (hs1 , hd1)
    = trans hs0 hs1 , trans hd0 hd1
\end{code}
%</Dmu-eq-trans-def>
