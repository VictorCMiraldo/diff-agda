\begin{code}
open import Prelude
open import Prelude.Monad
open import Diffing.Universe

module Diffing.Patches.Diff.D where

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


\begin{code}
  mutual
\end{code}
%<*D-to-delta>
\begin{code}
    D-Δ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
        → D A t ty → Maybe (ElU ty t × ElU ty t)
    D-Δ (D-A x) = nothing
    D-Δ D-unit = return (unit , unit)
    D-Δ (D-inl p) = (inl ×' inl) <M> D-Δ p
    D-Δ (D-inr p) = (inr ×' inr) <M> D-Δ p
    D-Δ (D-setl x x₁) = return (inl x , inr x₁)
    D-Δ (D-setr x x₁) = return (inr x , inl x₁)
    D-Δ (D-pair p p₁)
      = (λ s d → (p1 s , p1 d) , (p2 s , p2 d))
        <M> D-Δ p <M*> D-Δ p₁
    D-Δ (D-mu x) = Dμ-Δ x >>= (λ l → _,_ <M> lhead (p1 l) <M*> lhead (p2 l))
    D-Δ (D-def p) = (red ×' red) <M> D-Δ p
    D-Δ (D-top p) = (top ×' top) <M> D-Δ p
    D-Δ (D-pop p) = (pop ×' pop) <M> D-Δ p
\end{code}
%</D-to-delta>

%<*Dmu-to-delta>
\begin{code}
    Dμ-Δ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
        → List (Dμ A t ty) → Maybe (List (ElU (μ ty) t) × List (ElU (μ ty) t))
    Dμ-Δ [] = return ([] , [])
    Dμ-Δ (Dμ-A x ∷ p) = nothing
    Dμ-Δ (Dμ-ins x ∷ p)
      with Dμ-Δ p
    ...| just (sp , dp) = _,_ sp <M> (μ-close x dp >>= (return ∘ cons))
    ...| nothing        = nothing
    Dμ-Δ (Dμ-del x ∷ p)
      with Dμ-Δ p
    ...| just (sp , dp) = (λ ss → ss , dp) <M> (μ-close x sp >>= (return ∘ cons))
    ...| nothing        = nothing
    Dμ-Δ (Dμ-dwn x ∷ p)
      with D-Δ x | Dμ-Δ p
    ...| nothing        | _              = nothing
    ...| _              | nothing        = nothing
    ...| just (sx , dx) | just (sp , dp)
       = _,_ <M> (μ-close sx sp >>= (return ∘ cons)) <M*> (μ-close dx dp >>= (return ∘ cons))
\end{code}
%</Dmu-to-delta>

  Let's postulate some isomorphisms for the sake of
  progressing development. These proofs are mechanical.

\begin{code}
  postulate
    src-dst-Δ-lemma
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
      → (x y : ElU ty t)(p : D A t ty)
      → D-src p ≡ just x
      → D-dst p ≡ just y
      → D-Δ p ≡ just (x , y)

    Δ-src-dst-lemma
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
      → (x y : ElU ty t)(p : D A t ty)
      → D-Δ p ≡ just (x , y)
      → (D-src p ≡ just x) × (D-dst p ≡ just y)   
\end{code}

begin{code}
  src-dst-Δ-lemma x y (D-A x₁) () hy
  src-dst-Δ-lemma unit unit D-unit hx hy = refl
  src-dst-Δ-lemma x y (D-inl p) hx hy
    with D-src p | inspect D-src p
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hx))
  ...| just sp | [ SP ]
    with D-dst p | inspect D-dst p
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hy))
  ...| just dp | [ DP ]
     rewrite just-inj (sym hx)
           | just-inj (sym hy)
           = <M>-intro (src-dst-Δ-lemma sp dp p SP DP)
  src-dst-Δ-lemma x y (D-inr p) hx hy
    with D-src p | inspect D-src p
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hx))
  ...| just sp | [ SP ]
    with D-dst p | inspect D-dst p
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hy))
  ...| just dp | [ DP ]
     rewrite just-inj (sym hx)
           | just-inj (sym hy)
           = <M>-intro (src-dst-Δ-lemma sp dp p SP DP)
  src-dst-Δ-lemma .(inl xa) .(inr xb) (D-setl xa xb) refl refl = refl
  src-dst-Δ-lemma .(inr xa) .(inl xb) (D-setr xa xb) refl refl = refl
  src-dst-Δ-lemma x y (D-def p) hx hy
    with <M>-elim hx | <M>-elim hy
  ...| hx0 , hx1 , hx2 | hy0 , hy1 , hy2
    rewrite hx1 | hy1
      = <M>-intro (src-dst-Δ-lemma hx0 hy0 p hx2 hy2)
  src-dst-Δ-lemma x y (D-top p) hx hy
    with <M>-elim hx | <M>-elim hy
  ...| hx0 , hx1 , hx2 | hy0 , hy1 , hy2
    rewrite hx1 | hy1
      = <M>-intro (src-dst-Δ-lemma hx0 hy0 p hx2 hy2)
  src-dst-Δ-lemma x y (D-pop p) hx hy
    with <M>-elim hx | <M>-elim hy
  ...| hx0 , hx1 , hx2 | hy0 , hy1 , hy2
    rewrite hx1 | hy1
      = <M>-intro (src-dst-Δ-lemma hx0 hy0 p hx2 hy2)
  src-dst-Δ-lemma x y (D-pair p p₁) hx hy
    with D-Δ p
  ...| nothing        = {!!}
  ...| just (sp , dp) = {!!}
  src-dst-Δ-lemma x y (D-mu x₁) hx hy = {!!}
  
end{code}
