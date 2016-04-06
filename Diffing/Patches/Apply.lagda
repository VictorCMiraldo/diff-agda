\begin{code}
{-# OPTIONS --rewriting #-}
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
  gapplyL {i = suc i} {j = suc j} (Dμ-dwn .(μ-hd x) ey p) (x ∷ xs)
     | yes refl = μ-closev ey <M> gapplyL p (μ-chv x ++v xs)
  
\end{code}
%</gapplyL-def>

\begin{code}
  open import Diffing.Universe.Plugging.Properties
  {-# REWRITE ch-plugv-lemma #-}
  {-# REWRITE fgt-plugv-lemma #-}
\end{code}

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
    aux1 : {n i : ℕ}{t : T n}{ty : U (suc n)}
         → (a : ValU ty t)(v : Vec (ElU (μ ty) t) (ar 0 a + i))
         → μ-hd (mu (plugv 0 a (vmap pop (p1 (vsplit (ar 0 a) v))))) ≡ a
    aux1 a v = fgt-plugv-lemma 0 a
                     (vmap pop (p1 (vsplit (ar 0 a) v)))

    hd-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x : Dμ ⊥ₚ t ty 1 1)
             → head (Dμ-srcv x) ∷ [] ≡ Dμ-srcv x
    hd-lemma x with Dμ-srcv x
    hd-lemma x | e ∷ [] = refl

    aux-lemma-2
      : {n k : ℕ}{t : T n}{a : U n}{ty : U n}(v : Vec (ElU ty t) k)
      → {p : length (toList (vmap (pop {a = a}) v)) ≡ k}
      → vmap unpop (vec (toList (vmap pop v)) p) ≡ v
    aux-lemma-2 v {p} 
      = trans (cong (vmap unpop) 
                    (trans (vec-reduce (toList (vmap pop v))) 
                           (vec-toList (vmap pop v))))
              (vmap-lemma v (λ _ → refl))

  private
    aux-lemma-1 : {n i j : ℕ}{t : T n}{ty : U (suc n)}
                → (a : ValU ty t)(p : Dμ ⊥ₚ t ty (ar 0 a + i) j)
                → Dμ-srcv p
                ≡ μ-chv
                  (mu (plugv 0 a (vmap pop (p1 (vsplit (ar 0 a) (Dμ-srcv p))))))
                  ++v p2 (vsplit (ar 0 a) (Dμ-srcv p))
    aux-lemma-1 a p with vsplit (ar 0 a) (Dμ-srcv p) | inspect (vsplit (ar 0 a)) (Dμ-srcv p)
    ...| P0 , P1 | [ R ] 
       = sym (trans (cong (λ Q → Q ++v P1) (aux-lemma-2 P0)) 
                    (sym (vsplit-lemma P0 P1 (Dμ-srcv p) R)) )
\end{code}
%<*gapplyL-correct-def>
\begin{code}
  gapplyL-correct (Dμ-A () p)
  gapplyL-correct Dμ-end = refl
  gapplyL-correct {n} {suc i} {suc j} {t} {ty} (Dμ-dwn a b p)
    with μ-hd (mu (plugv 0 a (vmap pop (p1 (vsplit (ar 0 a) (Dμ-srcv p))))))
         ≟-U a
  ...| no  abs = ⊥-elim (abs (aux1 a (Dμ-srcv p)))
  ...| yes refl = sym (trans (sym (<M>-intro {f = μ-closev b} (gapplyL-correct p)))
                             (cong (_<M>_ (μ-closev b)) (cong (gapplyL p) 
                               (aux-lemma-1 a p)))) 
  gapplyL-correct (Dμ-del a p)
    with μ-hd (mu (plugv 0 a (vmap pop (p1 (vsplit (ar 0 a) (Dμ-srcv p))))))
         ≟-U a
  ...| no  abs  = ⊥-elim (abs (aux1 a (Dμ-srcv p)))
  ...| yes refl = trans (cong (gapplyL p) (sym (aux-lemma-1 a p))) (gapplyL-correct p) 
  gapplyL-correct (Dμ-ins a p) 
    rewrite gapplyL-correct p = refl
\end{code}
%</gapplyL-correct-def>
%<*gapply-correct-def>
\begin{code}
  gapply-correct (D-A ())
  gapply-correct D-unit = refl
  gapply-correct (D-inl p) 
    rewrite gapply-correct p = refl
  gapply-correct (D-inr p) 
    rewrite gapply-correct p = refl
  gapply-correct (D-setl x y) 
    rewrite ≟-U-refl x = refl
  gapply-correct (D-setr x y)
    rewrite ≟-U-refl x = refl
  gapply-correct (D-pair p q) 
    rewrite gapply-correct p
          | gapply-correct q
          = refl
  gapply-correct (D-mu x)
    = <M>-intro (subst (λ P → gapplyL x P ≡ just (Dμ-dstv x)) 
                (sym (hd-lemma x)) (gapplyL-correct x))     
  gapply-correct (D-def p)
    rewrite gapply-correct p = refl
  gapply-correct (D-top p) 
    rewrite gapply-correct p = refl
  gapply-correct (D-pop p)
    rewrite gapply-correct p = refl
\end{code}
%</gapply-correct-def>
