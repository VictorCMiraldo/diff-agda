\begin{code}
open import Prelude
open import Data.List.Properties using (length-++)
open import Diffing.Universe
open import Diffing.Utils.Vector

module Diffing.Patches.Diff.D where
\end{code}

%<*ValU>
\begin{code}
  ValU : {n : ℕ} → U (suc n) → T n → Set
  ValU ty t = ElU ty (u1 ∷ t)
\end{code}
%</ValU>

%<*Dmu-type>
\begin{code}
  data Dμ {a}(A : {n : ℕ} → T n → U n → Set a)
          {n : ℕ}(t : T n)(ty : U (suc n)) : ℕ → ℕ → Set a 
       where
\end{code}
%</Dmu-type>
%<*Dmu-A-def>
\begin{code}
    Dμ-A   : {i j : ℕ}
           → A t (μ ty) → Dμ A t ty i j → Dμ A t ty i j
\end{code}
%</Dmu-A-def>
%<*Dmu-end-def>
\begin{code}
    Dμ-end : Dμ A t ty 0 0
\end{code}
%</Dmu-end-def>
%<*Dmu-dwn-def>
\begin{code}
    Dμ-dwn : {i j : ℕ}(a : ValU ty t)(b : ValU ty t)
           → Dμ A t ty (ar 0 a + i) (ar 0 b + j)
           → Dμ A t ty (suc i) (suc j)
\end{code}
%</Dmu-dwn-def>
%<*Dmu-def>
\begin{code}
    Dμ-del : {i j : ℕ}(a : ValU ty t) 
           → Dμ A t ty (ar 0 a + i) j → Dμ A t ty (suc i) j
    Dμ-ins : {i j : ℕ}(a : ValU ty t) 
           → Dμ A t ty i (ar 0 a + j) → Dμ A t ty i (suc j)
\end{code}
%</Dmu-def>

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
%<*D-void-def>
\begin{code}
    D-unit : {n : ℕ}{t : T n} → D A t u1
\end{code}
%</D-void-def>
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
         → Dμ A t a 1 1 → D A t (μ a)
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

  Some synonyms for patches.

%<*Patch-def>
\begin{code}
  ⊥ₚ : {n : ℕ} → T n → U n → Set
  ⊥ₚ {_} _ _ = ⊥

  Patch : {n : ℕ} → T n → U n → Set
  Patch t ty = D ⊥ₚ t ty
       
  Patchμ : {n : ℕ} → T n → U (suc n) → Set
  Patchμ t ty = Dμ ⊥ₚ t ty 1 1
\end{code}
%</Patch-def>

  A Patch has both a src and a destination;

%<*D-src-type>
\begin{code}
  D-src : {n : ℕ}{t : T n}{ty : U n}
        → D ⊥ₚ t ty → ElU ty t
\end{code}
%</D-src-type>
%<*Dmu-src-type>
\begin{code}
  Dμ-srcv : {n i j : ℕ}{t : T n}{ty : U (suc n)}
          → Dμ ⊥ₚ t ty i j → Vec (ElU (μ ty) t) i
\end{code}
%</Dmu-src-type>
%<*Dmu-srcv-def>
\begin{code}
  Dμ-srcv (Dμ-A () d)
  Dμ-srcv (Dμ-del a d) = μ-closev a (Dμ-srcv d)
  Dμ-srcv (Dμ-ins a d) = Dμ-srcv d
  Dμ-srcv (Dμ-dwn a b d) = μ-closev a (Dμ-srcv d)
  Dμ-srcv Dμ-end = []
\end{code}
%</Dmu-srcv-def>
%<*Dmu-src-def>
\begin{code}
  Dμ-src : {n i j : ℕ}{t : T n}{ty : U (suc n)}
         → Dμ ⊥ₚ t ty i j → List (ElU (μ ty) t)
  Dμ-src = toList ∘ Dμ-srcv
\end{code}
%</Dmu-src-def>
%<*D-src-def>
\begin{code}
  D-src (D-A ())
  D-src D-unit = unit
  D-src (D-inl d) = inl (D-src d)
  D-src (D-inr d) = inr (D-src d)
  D-src (D-setl x _) = inl x
  D-src (D-setr x _) = inr x
  D-src (D-pair d e) = D-src d , D-src e
  D-src (D-mu x) = head (Dμ-srcv x)
  D-src (D-def d) = red (D-src d)
  D-src (D-top d) = top (D-src d)
  D-src (D-pop d) = pop (D-src d)
\end{code}
%</D-src-def>
%<*D-dst-type>
\begin{code}
  D-dst : {n : ℕ}{t : T n}{ty : U n}
        → D ⊥ₚ t ty → ElU ty t
\end{code}
%</D-dst-type>
%<*Dmu-dstv-type>
\begin{code}
  Dμ-dstv : {n i j : ℕ}{t : T n}{ty : U (suc n)}
         → Dμ ⊥ₚ t ty i j → Vec (ElU (μ ty) t) j
\end{code}
%</Dmu-dstv-type>
%<*Dmu-dstv-def>
\begin{code}
  Dμ-dstv (Dμ-A () d)
  Dμ-dstv (Dμ-del a d) = Dμ-dstv d
  Dμ-dstv (Dμ-ins a d) = μ-closev a (Dμ-dstv d)
  Dμ-dstv (Dμ-dwn a b d) = μ-closev b (Dμ-dstv d)
  Dμ-dstv Dμ-end = []
\end{code}
%</Dmu-dstv-def>
%<*Dmu-dst-def>
\begin{code}
  Dμ-dst : {n i j : ℕ}{t : T n}{ty : U (suc n)}
         → Dμ ⊥ₚ t ty i j → List (ElU (μ ty) t)
  Dμ-dst = toList ∘ Dμ-dstv
\end{code}
%</Dmu-src-def>
%<*D-dst-def>
\begin{code}
  D-dst (D-A ())
  D-dst D-unit = unit
  D-dst (D-inl d) = inl (D-dst d)
  D-dst (D-inr d) = inr (D-dst d)
  D-dst (D-setl _ x) = inr x
  D-dst (D-setr _ x) = inl x
  D-dst (D-pair d e) = D-dst d , D-dst e
  D-dst (D-mu x) = head (Dμ-dstv x)
  D-dst (D-def d) = red (D-dst d)
  D-dst (D-top d) = top (D-dst d)
  D-dst (D-pop d) = pop (D-dst d)
\end{code}
%</D-dst-def>

\begin{code}
  μ-length-arity-lemma
    : {n : ℕ}{t : T n}{ty : U (suc n)}
    → (y : ElU (μ ty) t)(ys : List (ElU (μ ty) t))
    → length (μ-ch y ++ ys) ≡ μ-ar y + length ys
  μ-length-arity-lemma y ys 
    = trans (length-++ (μ-ch y)) (cong₂ _+_ (μ-open-ar-lemma y) refl)

  μ-lal
    : {n : ℕ}{t : T n}{ty : U (suc n)}
    → {ys : List (ElU (μ ty) t)}(y : ElU (μ ty) t)
    → length (μ-ch y ++ ys) ≡ μ-ar y + length ys
  μ-lal {ys = ys} y = μ-length-arity-lemma y ys

  μ-lal-sym
    : {n : ℕ}{t : T n}{ty : U (suc n)}
    → {ys : List (ElU (μ ty) t)}(y : ElU (μ ty) t)
    → μ-ar y + length ys ≡ length (p2 (μ-open y) ++ ys)
  μ-lal-sym {ys = ys} y = sym (μ-length-arity-lemma y ys)
\end{code}
  

  Finally, a bunch of usefull lemmas to manipulate indices
  and call some well-known facts (meaning that we proved their
  general version on Diffing.Universe.Operations.Properties)

begin{code}
  module μ-subst where

    i : {n i j k : ℕ}{t : T n}{ty : U (suc n)}
            → k ≡ i
            → Dμ ⊥ₚ t ty k j
            → Dμ ⊥ₚ t ty i j
    i refl x = x

    i-elim
      : {n h j k : ℕ}{t : T n}{ty : U (suc n)}
      → (p : k ≡ h)(d : Dμ ⊥ₚ t ty k j)
      → i p d ≅ d
    i-elim refl d = HErefl

    o : {n h j k : ℕ}{t : T n}{ty : U (suc n)}
            → k ≡ h
            → Dμ ⊥ₚ t ty j k 
            → Dμ ⊥ₚ t ty j h
    o refl x = x

    o-elim
      : {n h j k : ℕ}{t : T n}{ty : U (suc n)}
      → (p : k ≡ h)(d : Dμ ⊥ₚ t ty j k)
      → o p d ≅ d
    o-elim refl x = HErefl

    io : {n h j k l : ℕ}{t : T n}{ty : U (suc n)}
               → l ≡ j
               → k ≡ h
               → Dμ ⊥ₚ t ty l k 
               → Dμ ⊥ₚ t ty j h
    io refl refl x = x

    io-elim
      : {n h j k l : ℕ}{t : T n}{ty : U (suc n)}
      → (p : k ≡ h)(q : l ≡ j)(d : Dμ ⊥ₚ t ty k l)
      → io p q d ≅ d
    io-elim refl refl d = HErefl
end{code}
