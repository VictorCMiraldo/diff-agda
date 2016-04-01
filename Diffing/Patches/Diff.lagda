\begin{code}
{-# OPTIONS --rewriting #-}
open import Prelude
open import Diffing.Universe
open import Diffing.Utils.Vector

module Diffing.Patches.Diff where

  open import Diffing.Patches.Diff.D public
  open import Diffing.Patches.Diff.Cost public
\end{code}

          Diffing
  =======================

  The type-safe variant of the diff algorithm is defined just like
  its type-UNsafe cousin.

  We do need, however, a bunch of lemmas to manipulate the indices of Dμ
  in order to make Agda happy.

  We start by declaring both gdiff and gdiffL

%<*gdiff-type>
\begin{code}
  {-# TERMINATING #-}
  gdiff : {n : ℕ}{t : T n}{ty : U n} 
        → ElU ty t → ElU ty t → Patch t ty
\end{code}
%</gdiff-type>
%<*gdiffL-type>
\begin{code}
  gdiffL : {n : ℕ}{t : T n}{ty : U (suc n)} 
         → (xs ys : List (ElU (μ ty) t)) → Dμ ⊥ₚ t ty (length xs) (length ys)
\end{code}
%</gdiffL-type>

  Before the actual diffing algorithm, we still need
  to populate our bag of tricks.

  Now we can define auxiliar functions for computing recursive diffs
  AND taking care of their indicies.

\begin{code}
  {-# REWRITE μ-lal-sym #-}
  gdiffL-ins : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (length xs) (suc (length ys))
  gdiffL-ins y xs ys = Dμ-ins (μ-hd y) (gdiffL xs (μ-ch y ++ ys))

  gdiffL-del : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (suc (length xs)) (length ys)
  gdiffL-del x xs ys = Dμ-del (μ-hd x) (gdiffL (μ-ch x ++ xs) ys)

  gdiffL-dwn : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (suc (length xs)) (suc (length ys))
  gdiffL-dwn x y xs ys 
    = Dμ-dwn (μ-hd x) (μ-hd y) (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys))
\end{code}

  Finally, the actual diffing algorithm.

%<*gdiff-def>
\begin{code}
  gdiff {ty = var} (top a) (top b)    = D-top (gdiff a b)
  gdiff {ty = wk u} (pop a) (pop b)  = D-pop (gdiff a b)
  gdiff {ty = def F x} (red a) (red b) = D-def (gdiff a b)
  gdiff {ty = u1} unit unit = D-unit
  gdiff {ty = ty ⊗ tv} (ay , av) (by , bv) 
    = D-pair (gdiff ay by) (gdiff av bv)
  gdiff {ty = ty ⊕ tv} (inl ay) (inl by) = D-inl (gdiff ay by)
  gdiff {ty = ty ⊕ tv} (inr av) (inr bv) = D-inr (gdiff av bv)
  gdiff {ty = ty ⊕ tv} (inl ay) (inr bv) = D-setl ay bv
  gdiff {ty = ty ⊕ tv} (inr av) (inl by) = D-setr av by
  gdiff {ty = μ ty} a b = D-mu (gdiffL (a ∷ []) (b ∷ []))
\end{code}
%</gdiff-def>
%<*gdiffL-def>
\begin{code}
  gdiffL [] [] = Dμ-end
  gdiffL [] (y ∷ ys) = gdiffL-ins y [] ys
  gdiffL (x ∷ xs) [] = gdiffL-del x xs [] 
  gdiffL (x ∷ xs) (y ∷ ys) 
    =  gdiffL-ins y (x ∷ xs) ys 
    ⊓μ gdiffL-del x xs (y ∷ ys)
    ⊓μ gdiffL-dwn x y xs ys
\end{code}
%</gdiffL-def>

        Application
  =======================

  Application follows the same idea. We first declare everything;
  we then prove auxiliar lemmas and define the apply function.

\begin{code}
  open import Diffing.Utils.Monads
  open Monad {{...}}

  {-# TERMINATING #-}
\end{code}

  Here we have the gapply and gapplyL declarations.

%<*gapplyL-type>
\begin{code}
  gapplyL : {n i j : ℕ}{t : T n}{ty : U (suc n)}
          → Dμ ⊥ₚ t ty i j 
          → Vec (ElU (μ ty) t) i → Maybe (Vec (ElU (μ ty) t) j)
\end{code}
%</gapplyL-type>
\end{code}
%<*gapply-type>
\begin{code}
  gapply : {n : ℕ}{t : T n}{ty : U n}
         → Patch t ty → ElU ty t → Maybe (ElU ty t)
\end{code}
%</gapply-type>

  Implementing gapply is easy.

%<*gapply-def>
\begin{code}
  gapply (D-A ())

  gapply D-unit unit = just unit

  gapply (D-inl diff) (inl el) = inl <M> gapply diff el
  gapply (D-inl diff) (inr el) = nothing

  gapply (D-inr diff) (inl el) = nothing
  gapply (D-inr diff) (inr el) = inr <M> gapply diff el

  gapply (D-setl x y) (inl el) with x ≟-U el
  ...| yes _ = just (inr y)
  ...| no  _ = nothing
  gapply (D-setl _ _) (inr _) = nothing

  gapply (D-setr y x) (inr el) with y ≟-U el
  ...| yes _ = just (inl x)
  ...| no  _ = nothing
  gapply (D-setr _ _) (inl _) = nothing

  gapply (D-pair da db) (a , b) with gapply da a
  ...| nothing = nothing
  ...| just ra = _,_ ra <M> gapply db b

  gapply (D-def diff) (red el) = red <M> gapply diff el
  gapply (D-top diff) (top el) = top <M> gapply diff el
  gapply (D-pop diff) (pop el) = pop <M> gapply diff el

  gapply {ty = μ ty} (D-mu d) el = head <M> gapplyL d (el ∷ [])
\end{code}
%</gapply-def>
\begin{code}
  apply-dwn-fix : {n i : ℕ}{t : T n}{ty : U (suc n)}
                → (x : ElU (μ ty) t)(ex : ValU ty t)
                → (hip : μ-hd x ≡ ex)
                → Vec (ElU (μ ty) t) (μ-ar x + i)
                → Vec (ElU (μ ty) t) (ar 0 ex + i)
  apply-dwn-fix x .(μ-hd x) refl v = v
\end{code}
%<*gapplyL-def>
\begin{code}
  gapplyL (Dμ-A () p) xs
  gapplyL Dμ-end [] = just []
  gapplyL (Dμ-del a p) (x ∷ xs) 
    with μ-hd x ≟-U a
  gapplyL (Dμ-del .(μ-hd x) p) (x ∷ xs) 
    | yes refl = gapplyL p (μ-chv x ++v xs)
  gapplyL (Dμ-del a p) (x ∷ xs) 
    | no  _ = nothing
  gapplyL (Dμ-ins a p) xs 
    = μ-closev a <M> gapplyL p xs
  gapplyL {i = suc i} {j = suc j} {t} {ty} (Dμ-dwn ex ey p) (x ∷ xs) 
    with μ-hd x ≟-U ex
  ...| no  _ = nothing
  -- ...| yes q = μ-closev ey <M> gapplyL p (apply-dwn-fix x ex q (μ-chv x ++v xs))
  gapplyL {i = suc i} {j = suc j} (Dμ-dwn .(μ-hd x) ey p) (x ∷ xs)
     | yes refl = μ-closev ey <M> gapplyL p (μ-chv x ++v xs)
  
\end{code}
%</gapplyL-def>

