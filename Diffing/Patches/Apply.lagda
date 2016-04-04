\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Utils.Vector

module Diffing.Patches.Apply
  where

  open import Diffing.Patches.Diff.D
\end{code}


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

