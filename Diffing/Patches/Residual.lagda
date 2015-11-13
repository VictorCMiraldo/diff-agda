\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff

module Diffing.Patches.Residual where
\end{code}


  Let p and q be patches for a given datatype.
  A residual (p / q) means applying p AFTER the changes by
  q have been made. It encodes a notion of propagation.

  However, we cannot propagate the changes of p over q
  for any p and q. Some of them give rise to conflicts.

  Since a conflict arises when calculating the residual patch of (p / q),
  we'll call p the post-patch and q the pre-patch

%<*C-def>
\begin{code}
  data C : Set where
    UpdUpd : {n : ℕ}{t : Tel n}{a b : U n}
           → ElU a t → ElU b t → C
    DelUpd : {n : ℕ}{t : Tel n}{a b : U n}
           → ElU a t → ElU b t → C
    UpdDel : {n : ℕ}{t : Tel n}{a b : U n}
           → ElU a t → ElU b t → C
\end{code}
%</C-def>

A simple applicative style application combinator.

%<*conflict-app>
\begin{code}
  _<C>_ : {A B : Set} → (A → B) → Maybe (A ⊎ C) → Maybe (B ⊎ C)
  f <C> nothing     = nothing
  f <C> just (i1 x) = just (i1 (f x))
  f <C> just (i2 y) = just (i2 y)

  _<C*>_ : {A B : Set} → Maybe ((A → B) ⊎ C) → Maybe (A ⊎ C) → Maybe (B ⊎ C)
  nothing     <C*> _           = nothing
  just (i2 c) <C*> _           = just (i2 c)
  just (i1 f) <C*> nothing     = nothing
  just (i1 f) <C*> just (i2 c) = just (i2 c)
  just (i1 f) <C*> just (i1 a) = just (i1 (f a))

  infixl 20 _<C>_ _<C*>_
\end{code}
%</conflict-app>

 Finally, the actual residual definition.
 Note that the type of _/_ is a bit complicated.

 It only makes sense to calculate the residual of aligned patches,
 meaning that they must be defined for the same inputs.
 If (dx / dy) ≡ nothing, it means that dx and dy are NOT aligned.

 If (dx / dy) ≡ just (i2 c), it means that they are aligned, but conflicting.

 If (dx / dy) ≡ just (i1 res), it means that they are aligned and, moreover,
                             , a merge is given by res

%<*residual-type>
\begin{code}
  mutual
    {-# TERMINATING #-}
    _/_ : {n : ℕ}{t : Tel n}{ty : U n} 
        → D t ty → D t ty → Maybe (D t ty ⊎ C)
\end{code}
%</residual-type>
\begin{code}
    _/_ {ty = u1} p q = just (i1 D-void)

    _/_ {ty = a ⊕ b} (D-inl p) (D-inl q) = D-inl <C> (p / q)
    _/_ {ty = a ⊕ b} (D-inr p) (D-inr q) = D-inr <C> (p / q)
    
    _/_ {ty = a ⊕ b} (D-setl xa xb) (D-setl ya yb) with xa ≟-U ya
    ...| no  _ = nothing
    ...| yes _ with xb ≟-U yb
    ...| no  _ = just (i2 (UpdUpd xb yb))
    ...| yes _ = just (i1 (D-setl xa xb))
    _/_ {ty = a ⊕ b} (D-setr xa xb) (D-setr ya yb) with xa ≟-U ya
    ...| no  _ = nothing
    ...| yes _ with xb ≟-U yb
    ...| no  _ = just (i2 (UpdUpd xb yb))
    ...| yes _ = just (i1 (D-setr xa xb))

    _/_ {ty = a ⊕ b} (D-setl xa xb) (D-inl p) with gapply p xa
    ...| nothing = nothing
    ...| just xa' = just (i2 (UpdUpd xa' xb))
    _/_ {ty = a ⊕ b} (D-inl p) (D-setl xa xb) with gapply p xa
    ...| nothing = nothing
    ...| just xa' = just (i2 (UpdUpd xa' xb))
    _/_ {ty = a ⊕ b} (D-setr xa xb) (D-inr p) with gapply p xa
    ...| nothing = nothing
    ...| just xa' = just (i2 (UpdUpd xa' xb))
    _/_ {ty = a ⊕ b} (D-inr p) (D-setr xa xb) with gapply p xa
    ...| nothing = nothing
    ...| just xa' = just (i2 (UpdUpd xa' xb))

    _/_ {ty = a ⊗ b} (D-pair p1 p2) (D-pair q1 q2) 
      = D-pair <C> (p1 / q1) <C*> (p2 / q2)

    _/_ {ty = β F x} (D-β p) (D-β q) = D-β <C> (p / q)
    _/_ {ty = vl} (D-top p) (D-top q) = D-top <C> (p / q)
    _/_ {ty = wk ty} (D-pop p) (D-pop q) = D-pop <C> (p / q)

    _/_ {ty = μ ty} (D-mu p) (D-mu q) = D-mu <C> res p q

    -- Every other scenarios are non-aligned patches.
    _ / _ = nothing

    res : {n : ℕ}{t : Tel n}{ty : U (suc n)}
        → List (Dμ t ty) → List (Dμ t ty) → Maybe (List (Dμ t ty) ⊎ C)

    -- if both patches finishes together, easy.
    res [] [] = just (i1 [])
   
    -- we can always keep inserting things, though.
    -- If we find the same exact insert, though, we simply copy it.
    res (Dμ-ins x ∷ dp) (Dμ-ins y ∷ dq) with x ≟-U y
    ...| yes _ = _∷_ (Dμ-cpy x) <C> res dp dq
    ...| no  _ = _∷_ (Dμ-ins x) <C> res dp (Dμ-ins y ∷ dq)
    res dp (Dμ-ins x ∷ dq) = _∷_ (Dμ-cpy x) <C> res dp dq
    res (Dμ-ins x ∷ dp) dq = _∷_ (Dμ-ins x) <C> res dp dq
      
    -- Copies must be consistent.
    res (Dμ-cpy x ∷ dp) (Dμ-cpy y ∷ dq) with x ≟-U y
    ...| yes _ = _∷_ (Dμ-cpy x) <C> res dp dq
    ...| no  p = nothing 

    -- Erasing is a bit more tricky.
    res (Dμ-del x ∷ dp) (Dμ-cpy y ∷ dq) with x ≟-U y
    ...| yes _ = _∷_ (Dμ-del x) <C> res dp dq
    ...| no  p = nothing
    res (Dμ-cpy x ∷ dp) (Dμ-del y ∷ dq) with x ≟-U y
    ...| yes _ = res dp dq
    ...| no  p = nothing
    res (Dμ-del x ∷ dp) (Dμ-del y ∷ dq) with x ≟-U y
    ...| yes _ = res dp dq
    ...| no  p = nothing

    res (Dμ-dwn dx ∷ dp) (Dμ-cpy y ∷ dq) with gapply dx (red y)
    ...| just  _ = _∷_ (Dμ-dwn dx) <C> res dp dq
    ...| nothing = nothing
    res (Dμ-cpy x ∷ dp) (Dμ-dwn dy ∷ dq) with gapply dy (red x)
    ...| just (red x2) = _∷_ (Dμ-cpy x2) <C> res dp dq
    ...| nothing       = nothing
    res (Dμ-dwn dx ∷ dp) (Dμ-dwn dy ∷ dq)
      = _∷_ <C> (Dμ-dwn <C> (dx / dy)) <C*> res dp dq

    res (Dμ-dwn dx ∷ dp) (Dμ-del y ∷ dq) with gapply dx (red y)
    ...| just y'  = just (i2 (UpdDel y' (red y)))
    ...| nothing = nothing
    res (Dμ-del y ∷ dp) (Dμ-dwn dx ∷ dq) with gapply dx (red y)
    ...| just y'  = just (i2 (DelUpd (red y) y'))
    ...| nothing = nothing

    res [] _  = nothing
    res _ []  = nothing

\end{code}

%<*NoConflict>
\begin{code}
  NoConflict : ∀{a}{A : Set a} → A ⊎ C → Set
  NoConflict (i1 _) = Unit
  NoConflict (i2 _) = ⊥
\end{code}
%</NoConflict>

