\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff
open import Diffing.Patches.Diff.Functor using (cast; forget)
open import Diffing.Patches.Diff.Id
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
    _/_ : {n : ℕ}{t : Tel n}{ty : U n} 
        → Patch t ty → Patch t ty → Maybe (D C t ty)
\end{code}
%</residual-type>
\begin{code}
    _/_ {ty = u1} p q = just D-void

    _/_ {ty = a ⊕ b} (D-inl p) (D-inl q) = D-inl <M> (p / q)
    _/_ {ty = a ⊕ b} (D-inr p) (D-inr q) = D-inr <M> (p / q)
    
    _/_ {ty = a ⊕ b} (D-setl xa xb) (D-setl ya yb) with xa ≟-U ya
    ...| no  _ = nothing
    ...| yes _ with xb ≟-U yb
    ...| no  _ = just (D-A (UpdUpd (inl xa) (inr xb) (inr yb)))
    ...| yes _ = just (D-setl xa xb)
    _/_ {ty = a ⊕ b} (D-setr xa xb) (D-setr ya yb) with xa ≟-U ya
    ...| no  _ = nothing
    ...| yes _ with xb ≟-U yb
    ...| no  _ = just (D-A (UpdUpd (inr xa) (inl xb) (inl yb)))
    ...| yes _ = just (D-setr xa xb)

    _/_ {ty = a ⊕ b} (D-setl xa xb) (D-inl p) with gapply p xa
    ...| nothing = nothing
    ...| just xa' with xa ≟-U xa' 
    ...| no  _ = just (D-A (UpdUpd (inl xa) (inr xb) (inl xa')))
    ...| yes _ = just (D-setl xa xb)
    _/_ {ty = a ⊕ b} (D-inl p) (D-setl xa xb) with gapply p xa
    ...| nothing = nothing
    ...| just xa' with xa ≟-U xa' 
    ...| no  _ = just (D-A (UpdUpd (inl xa) (inl xa') (inr xb)))
    ...| yes _ = just (D-setl xa xb)
    _/_ {ty = a ⊕ b} (D-setr xa xb) (D-inr p) with gapply p xa
    ...| nothing = nothing
    ...| just xa' with xa ≟-U xa'
    ...| no  _ = just (D-A (UpdUpd (inr xa) (inl xb) (inr xa')))
    ...| yes _ = just (D-setr xa xb)
    _/_ {ty = a ⊕ b} (D-inr p) (D-setr xa xb) with gapply p xa
    ...| nothing = nothing
    ...| just xa' with xa ≟-U xa'
    ...| no  _ = just (D-A (UpdUpd (inr xa) (inr xa') (inl xb)))
    ...| yes _ = just (D-setr xa xb)

    _/_ {ty = a ⊗ b} (D-pair p1 p2) (D-pair q1 q2) 
      = D-pair <M> (p1 / q1) <M*> (p2 / q2)

    _/_ {ty = β F x} (D-β p) (D-β q) = D-β <M> (p / q)
    _/_ {ty = vl} (D-top p) (D-top q) = D-top <M> (p / q)
    _/_ {ty = wk ty} (D-pop p) (D-pop q) = D-pop <M> (p / q)

    _/_ {ty = μ ty} (D-mu p) (D-mu q) = D-mu <M> res p q

    -- Every other scenarios are non-aligned patches.
    _ / _ = nothing

    res : {n : ℕ}{t : Tel n}{ty : U (suc n)}
        → (a b : Patchμ t ty) → Maybe (List (Dμ C t ty))

    res _ (Dμ-A () ∷ _)
    res (Dμ-A () ∷ _) _

    -- if both patches finishes together, easy.
    res [] [] = just []
   
    -- we can always keep inserting things, though.
    -- If we find the same exact insert, though, we simply copy it.
    res (Dμ-ins x ∷ dp) (Dμ-ins y ∷ dq) with x ≟-U y
    ...| yes _ = _∷_ (Dμ-dwn (cast (gdiff-id x))) <M> res dp dq
    ...| no  _ = _∷_ (Dμ-A (GrowLR x y)) <M> res dp dq
    res dp (Dμ-ins x ∷ dq) = _∷_ (Dμ-A (GrowR x)) <M> res dp dq
    res (Dμ-ins x ∷ dp) dq = _∷_ (Dμ-A (GrowL x)) <M> res dp dq

    res (Dμ-del x ∷ dp) (Dμ-del y ∷ dq) with x ≟-U y
    ...| yes _ = res dp dq
    ...| no  p = nothing

    res (Dμ-dwn dx ∷ dp) (Dμ-dwn dy ∷ dq) 
      = _∷_ <M> (Dμ-dwn <M> (dx / dy)) <M*> res dp dq
\end{code}
%<*res-dwn-del-case>
\begin{code}
    res (Dμ-dwn dx ∷ dp) (Dμ-del y ∷ dq)
      with gapply dx y
    ...| nothing = nothing
    ...| just y' with y ≟-U y'
    ...| yes _ = res dp dq
    ...| no  _ = _∷_ (Dμ-A (UpdDel y' y)) <M> res dp dq    
\end{code}
%</res-dwn-del-case>
\begin{code}
    res (Dμ-del y ∷ dp) (Dμ-dwn dx ∷ dq)
      with gapply dx y
    ...| just y'  
       = dec-elim (λ _ → _∷_ (Dμ-del y) <M> res dp dq)
                  (λ _ → _∷_ (Dμ-A (DelUpd y y')) <M> res dp dq)
                  (y ≟-U y')
    ...| nothing = nothing

    res [] _  = nothing
    res _ []  = nothing
\end{code}

The simple residuals are the ones defined and
without conflicts!

\begin{code}
  /-simple : {n : ℕ}{t : Tel n}{ty : U n}
           → Maybe (D C t ty) → Set
  /-simple nothing  = ⊥
  /-simple (just d) = forget d ≡ []
\end{code}
