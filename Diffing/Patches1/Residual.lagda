\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches1.Diff
open import Diffing.Patches1.Diff.Functor using (cast)
open import Diffing.Patches1.Conflicts

module Diffing.Patches1.Residual where
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

%<*residual-type>
\begin{code}
  mutual
    {-# TERMINATING #-}
    _/_ : {n : ℕ}{t : Tel n}{ty : U n} 
        → Patch t ty → Patch t ty → Maybe (D C t ty)
\end{code}
%</residual-type>
\begin{code}
    _/_ D-id _ = just D-id
    _/_ p D-id = just (cast p)

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
    ...| yes _ = _∷_ (Dμ-cpy x) <M> res dp dq
    ...| no  _ = _∷_ (Dμ-A (GrowLR x y)) <M> res dp dq
    res dp (Dμ-ins x ∷ dq) = _∷_ (Dμ-A (GrowR x)) <M> res dp dq
    res (Dμ-ins x ∷ dp) dq = _∷_ (Dμ-A (GrowL x)) <M> res dp dq
      
    -- Copies must be consistent.
    res (Dμ-cpy x ∷ dp) (Dμ-cpy y ∷ dq) with x ≟-U y
    ...| yes _ = _∷_ (Dμ-cpy x) <M> res dp dq
    ...| no  p = nothing 

    -- Erasing is a bit more tricky.
    res (Dμ-del x ∷ dp) (Dμ-cpy y ∷ dq) with x ≟-U y
    ...| yes _ = _∷_ (Dμ-del x) <M> res dp dq
    ...| no  p = nothing
    res (Dμ-cpy x ∷ dp) (Dμ-del y ∷ dq) with x ≟-U y
    ...| yes _ = res dp dq
    ...| no  p = nothing
    res (Dμ-del x ∷ dp) (Dμ-del y ∷ dq) with x ≟-U y
    ...| yes _ = res dp dq
    ...| no  p = nothing

    res (Dμ-dwn x dx ∷ dp) (Dμ-cpy y ∷ dq) with x ≟-U y
    ...| no _ = nothing
    ...| yes _ with gapply dx (red y)
    ...| just  _ = _∷_ (Dμ-dwn x (cast dx)) <M> res dp dq
    ...| nothing = nothing
    res (Dμ-cpy x ∷ dp) (Dμ-dwn y dy ∷ dq) with x ≟-U y
    ...| no _ = nothing
    ...| yes _ with gapply dy (red x)
    ...| just (red x2) = _∷_ (Dμ-cpy x2) <M> res dp dq
    ...| nothing       = nothing
    res (Dμ-dwn x dx ∷ dp) (Dμ-dwn y dy ∷ dq) with x ≟-U y
    ...| no _ = nothing
    ...| yes _
      = _∷_ <M> (Dμ-dwn x <M> (dx / dy)) <M*> res dp dq

    res (Dμ-dwn x dx ∷ dp) (Dμ-del y ∷ dq) with x ≟-U y
    ...| no _ = nothing
    ...| yes _ with gapply dx (red y)
    ...| just (red y')  = _∷_ (Dμ-A (UpdDel y' y)) <M> res dp dq
    ...| nothing = nothing
    res (Dμ-del y ∷ dp) (Dμ-dwn x dx ∷ dq) with x ≟-U y
    ...| no _ = nothing
    ...| yes _ with gapply dx (red y)
    ...| just (red y')  = _∷_ (Dμ-A (DelUpd y y')) <M> res dp dq
    ...| nothing = nothing

    res [] _  = nothing
    res _ []  = nothing
\end{code}

  lemma /-id is just to make our life easier, as Agda
  does not recognize (d / D-id) ≡ just (cast d) through refl,
  as it needs to match the head of d.

\begin{code}
  /-id : {n : ℕ}{t : Tel n}{ty : U n}(d : Patch t ty)
          → (d / D-id) ≡ just (cast d)
  /-id (D-A ())
  /-id D-id = refl
  /-id D-void = refl
  /-id (D-inl d₁) = refl
  /-id (D-inr d₁) = refl
  /-id (D-setl x x₁) = refl
  /-id (D-setr x x₁) = refl
  /-id (D-pair d₁ d₂) = refl
  /-id (D-mu x) = refl
  /-id (D-β d₁) = refl
  /-id (D-top d₁) = refl
  /-id (D-pop d₁) = refl
\end{code}

