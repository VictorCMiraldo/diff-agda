\begin{code}
{-# OPTIONS --rewriting #-}
open import Prelude
open import Data.List.Properties
  using (length-++)
open import Diffing.Universe
open import Diffing.Universe.Operations.Properties
open import Diffing.Universe.Plugging.Properties
open import Diffing.Patches.Diff
open import Diffing.Utils.Vector

module Diffing.Patches.Diff.Correctness where

  open import Diffing.Utils.Monads
  open Monad {{...}}
\end{code}

  D-src and D-dst are projections for gdiff.

\begin{code}
  {-# TERMINATING #-}
\end{code}
%<*gdiffL-src-lemma-type>
\begin{code}
  gdiffL-src-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
                  → (x y : List (ElU (μ ty) t))
                  → Dμ-srcv (gdiffL x y) ≡ vec x refl
\end{code}
%</gdiffL-src-lemma-type>
\begin{code}
  private
    src-del : {n : ℕ}{t : T n}{ty : U (suc n)}
            → (x : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
            → Dμ-srcv (gdiffL-del x xs ys) ≡ vec (x ∷ xs) refl
    src-del x xs ys rewrite gdiffL-src-lemma (μ-ch x ++ xs) ys
      with vsplit-elim (μ-ch x) xs {p = μ-open-ar-++-lemma x xs} 
              {q₁ = μ-open-ar-lemma x } {q₂ = refl} 
    ...| prf rewrite ≡-pi (μ-open-ar-++-lemma x xs) refl | prf 
      = cong (λ P → P ∷ vec xs refl) (μ-plugv-correct x)

    src-dwn : {n : ℕ}{t : T n}{ty : U (suc n)}
            → (x y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
            → Dμ-srcv (gdiffL-dwn x y xs ys) ≡ vec (x ∷ xs) refl
    src-dwn x y xs ys rewrite gdiffL-src-lemma (μ-ch x ++ xs) (μ-ch y ++ ys)
      with vsplit-elim (μ-ch x) xs {p = μ-open-ar-++-lemma x xs} 
              {q₁ = μ-open-ar-lemma x } {q₂ = refl} 
    ...| prf rewrite ≡-pi (μ-open-ar-++-lemma x xs) refl | prf 
      = cong (λ P → P ∷ vec xs refl) (μ-plugv-correct x)
\end{code}
%<*gdiffL-src-lemma-def>
\begin{code}
  gdiffL-src-lemma [] []       = refl
  gdiffL-src-lemma [] (y ∷ ys) = gdiffL-src-lemma [] (μ-ch y ++ ys)
  gdiffL-src-lemma (x ∷ xs) [] = src-del x xs []
  gdiffL-src-lemma (x ∷ xs) (y ∷ ys) 
    = toList-vec-≡ (x ∷ xs) _
        (⊓μ-elim3 {P = λ p → toList (Dμ-srcv p) ≡ x ∷ xs}
         (gdiffL-ins y (x ∷ xs) ys) 
         (gdiffL-del x xs (y ∷ ys))
         (gdiffL-dwn x y xs ys) 
         (trans (cong toList (gdiffL-src-lemma (x ∷ xs) (μ-ch y ++ ys))) 
                (cong (_∷_ x) (toList-vec xs))) 
         (trans (cong toList (src-del x xs (y ∷ ys))) 
                (cong (_∷_ x) (toList-vec xs))) 
         (trans (cong toList (src-dwn x y xs ys)) 
                (cong (_∷_ x) (toList-vec xs))))
\end{code}
%</gdiffL-src-lemma-def>

%<*gdiff-src-lemma-type>
\begin{code}
  gdiff-src-lemma : {n : ℕ}{t : T n}{ty : U n}
                  → (x y : ElU ty t)
                  → D-src (gdiff x y) ≡ x
\end{code}
%</gdiff-src-lemma-type>
%<*gdiff-src-lemma-def>
\begin{code}
  gdiff-src-lemma unit unit = refl
  gdiff-src-lemma (inl x) (inl y) = cong inl (gdiff-src-lemma x y)
  gdiff-src-lemma (inl x) (inr y) = refl
  gdiff-src-lemma (inr x) (inl y) = refl
  gdiff-src-lemma (inr x) (inr y) = cong inr (gdiff-src-lemma x y)
  gdiff-src-lemma (x1 , x2) (y1 , y2) 
    = cong₂ _,_ (gdiff-src-lemma x1 y1) (gdiff-src-lemma x2 y2)
  gdiff-src-lemma (top x) (top y) = cong top (gdiff-src-lemma x y)
  gdiff-src-lemma (pop x) (pop y) = cong pop (gdiff-src-lemma x y)
  gdiff-src-lemma (red x) (red y) = cong red (gdiff-src-lemma x y)
  gdiff-src-lemma (mu x) (mu y) 
    = cong head (gdiffL-src-lemma (mu x ∷ []) (mu y ∷ []))
\end{code}
%</gdiff-src-lemma-def>

\begin{code}
  {-# TERMINATING #-}
\end{code}
%<*gdiffL-dst-lemma-type>
\begin{code}
  gdiffL-dst-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
                  → (x y : List (ElU (μ ty) t))
                  → Dμ-dstv (gdiffL x y) ≡ vec y refl
\end{code}
%</gdiffL-dst-lemma-type>
\begin{code}
  private
    dst-ins : {n : ℕ}{t : T n}{ty : U (suc n)}
            → (y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
            → Dμ-dstv (gdiffL-ins y xs ys) ≡ vec (y ∷ ys) refl
    dst-ins y xs ys rewrite gdiffL-dst-lemma xs (μ-ch y ++ ys)
      with vsplit-elim (μ-ch y) ys {p = μ-open-ar-++-lemma y ys} 
              {q₁ = μ-open-ar-lemma y} {q₂ = refl} 
    ...| prf rewrite ≡-pi (μ-open-ar-++-lemma y ys) refl | prf
       = cong (λ P → P ∷ vec ys refl) (μ-plugv-correct y)

    dst-dwn : {n : ℕ}{t : T n}{ty : U (suc n)}
            → (x y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
            → Dμ-dstv (gdiffL-dwn x y xs ys) ≡ vec (y ∷ ys) refl
    dst-dwn x y xs ys rewrite gdiffL-dst-lemma (μ-ch x ++ xs) (μ-ch y ++ ys)
      with vsplit-elim (μ-ch y) ys {p = μ-open-ar-++-lemma y ys} 
              {q₁ = μ-open-ar-lemma y} {q₂ = refl} 
    ...| prf rewrite ≡-pi (μ-open-ar-++-lemma y ys) refl | prf 
      = cong (λ P → P ∷ vec ys refl) (μ-plugv-correct y)
\end{code}
%<*gdiffL-dst-lemma-def>
\begin{code}
  gdiffL-dst-lemma [] []       = refl
  gdiffL-dst-lemma [] (y ∷ ys) = dst-ins y [] ys
  gdiffL-dst-lemma (x ∷ xs) [] = gdiffL-dst-lemma (μ-ch x ++ xs) []
  gdiffL-dst-lemma (x ∷ xs) (y ∷ ys) 
    = toList-vec-≡ (y ∷ ys) _
        (⊓μ-elim3 {P = λ p → toList (Dμ-dstv p) ≡ y ∷ ys}
         (gdiffL-ins y (x ∷ xs) ys) 
         (gdiffL-del x xs (y ∷ ys))
         (gdiffL-dwn x y xs ys) 
         (trans (cong toList (dst-ins y (x ∷ xs) ys)) 
                (cong (_∷_ y) (toList-vec ys)))
         (trans (cong toList (gdiffL-dst-lemma (μ-ch x ++ xs) (y ∷ ys))) 
                (cong (_∷_ y) (toList-vec ys))) 
         (trans (cong toList (dst-dwn x y xs ys)) 
                (cong (_∷_ y) (toList-vec ys))))
\end{code}
%</gdiffL-dst-lemma-def>

%<*gdiff-dst-lemma-type>
\begin{code}
  gdiff-dst-lemma : {n : ℕ}{t : T n}{ty : U n}
                  → (x y : ElU ty t)
                  → D-dst (gdiff x y) ≡ y
\end{code}
%</gdiff-dst-lemma-type>
%<*gdiff-dst-lemma-def>
\begin{code}
  gdiff-dst-lemma unit unit = refl
  gdiff-dst-lemma (inl x) (inl y) = cong inl (gdiff-dst-lemma x y)
  gdiff-dst-lemma (inl x) (inr y) = refl
  gdiff-dst-lemma (inr x) (inl y) = refl
  gdiff-dst-lemma (inr x) (inr y) = cong inr (gdiff-dst-lemma x y)
  gdiff-dst-lemma (x1 , x2) (y1 , y2) 
    = cong₂ _,_ (gdiff-dst-lemma x1 y1) (gdiff-dst-lemma x2 y2)
  gdiff-dst-lemma (top x) (top y) = cong top (gdiff-dst-lemma x y)
  gdiff-dst-lemma (pop x) (pop y) = cong pop (gdiff-dst-lemma x y)
  gdiff-dst-lemma (red x) (red y) = cong red (gdiff-dst-lemma x y)
  gdiff-dst-lemma (mu x) (mu y) 
    = cong head (gdiffL-dst-lemma (mu x ∷ []) (mu y ∷ []))
\end{code}
%</gdiff-dst-lemma-def>

  Now that we know that a patch has both a source and a destination,
  moreover, gdiff is the algorithm that construct the patch from
  the source and the destination; we just need to make sure that
  applying a patch to it's source will always yield its destination.

%<*gapply-correct-type>
\begin{code}
  gapply-correct : {n : ℕ}{t : T n}{ty : U n}
                 → (p : D ⊥ₚ t ty)
                 → gapply p (D-src p) ≡ just (D-dst p)
\end{code}
%</gapply-correct-type>
%<*gapplyL-correct-type>
\begin{code}
  gapplyL-correct : {n i j : ℕ}{t : T n}{ty : U (suc n)}
                  → (p : Dμ ⊥ₚ t ty i j)
                  → gapplyL p (Dμ-srcv p) ≡ just (Dμ-dstv p)
\end{code}
%</gapplyL-correct-type>
\begin{code}
  private
    open import Relation.Binary.PropositionalEquality.TrustMe

    aux1 : {n i : ℕ}{t : T n}{ty : U (suc n)}
         → (a : ValU ty t)(v : Vec (ElU (μ ty) t) (ar 0 a + i))
         → μ-hd (mu (plugv 0 a (vmap pop (p1 (vsplit (ar 0 a) v))))) ≡ a
    aux1 a v = fgt-plugv-lemma 0 a
                     (vmap pop (p1 (vsplit (ar 0 a) v)))
\end{code}
%<*gapplyL-correct-def>
\begin{code}
  gapplyL-correct (Dμ-A () p)
  gapplyL-correct Dμ-end = refl
  gapplyL-correct {n} {suc i} {suc j} {t} {ty} (Dμ-dwn a b p) 
    rewrite ≟-U-≡ (aux1 a (Dμ-srcv p)) 
          = {!gapplyL-correct p!}
  {-
    rewrite fgt-plugv-lemma 0 a
                     (vmap pop (p1 (vsplit (ar 0 a) (Dμ-srcv p))))
           = ?
  -}
  gapplyL-correct (Dμ-del a p) = {!!}
  gapplyL-correct (Dμ-ins a p) = {!!}
\end{code}
%</gapplyL-correct-def>
%<*gapply-correct-def>
\begin{code}
  gapply-correct p = {!!}
\end{code}
%</gapply-correct-def>
