\begin{code}
open import Prelude
open import Diffing.Universe

open import Diffing.Patches.Diff
open import Diffing.Patches.Diff.Functor using (cast; forget)
open import Diffing.Patches.Diff.Id
open import Diffing.Patches.Diff.Alignment
open import Diffing.Patches.Conflicts

module Diffing.Patches.Residual where
\end{code}

  Residuals are the heart of a merge. the patch (p / q),
  if defined, is the patch that incorporates the changes
  that p did, but on an object already altered by q.

  The simplified (informal) diagram is:

                    A₁
                p ↙    ↘ q
                A₂      A₃
            (q/p) ↘    ↙ (p/q) 
                    A₄

  It only makes sense to calculate the residual of aligned patches,
  meaning that they must be defined for the same inputs.

  Here we use some sort of trick to comply with that notion.
  We define alignment on top of _/_. That is,
  we say that two patches p and q are aligned iff (p/q) is just x, for some x.

  If (dx / dy) ≡ nothing, it means that dx and dy are NOT aligned.

  If (dx / dy) ≡ just k, it means that dx and dy are aligned and
                         a merge is given by k. 

  Note that upon having (dx / dy) ≡ just k, it is not always the case
  that they merge peacefully. k might contain conflicts inside!

\begin{code}
  mutual
    {-# TERMINATING #-}
\end{code}
%<*residual-type>
\begin{code}
    res : {n : ℕ}{t : T n}{ty : U n}
        → (p q : Patch t ty)(hip : p || q)
        → D C t ty
\end{code}
%</residual-type>
\begin{code}
    res (D-A ()) q hip
    res p (D-A ()) hip
    res D-unit D-unit hip = D-unit
    res {ty = ty ⊕ tv} (D-inl p) (D-inl q) hip
      = D-inl (res p q (||-inl-elim {p = p} {q = q} hip))
    res (D-inl p) (D-setl xa xb) hip = {!!}
    
    res (D-inl p) (D-inr q)     hip = {!!}
    res (D-inl p) (D-setr x x₁) hip = {!!}
    
    res (D-inr p) q hip = {!!}
    res (D-setl x x₁) q hip = {!!}
    res (D-setr x x₁) q hip = {!!}
    res (D-pair p p₁) q hip = {!!}
    res (D-mu x) q hip = {!!}
    res (D-def p) q hip = {!!}
    res (D-top p) q hip = {!!}
    res (D-pop p) q hip = {!!}
    

    resμ : {n : ℕ}{t : T n}{ty : U (suc n)}
         → (ps qs : Patchμ t ty) → ps ||μ qs → List (Dμ C t ty)

    resμ ps qs = {!!}
\end{code}

