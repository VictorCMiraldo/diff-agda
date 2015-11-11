\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff

module Diffing.Residual where
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
    -- One patch goes through the left, the other through the right.
    C-LR : {n : ℕ}{t : Tel n}{a b : U n} → D t a → D t b → C
    
    -- Both patches are setting different values.
    C-SetSet : {n : ℕ}{t : Tel n}{a b : U n} → ElU a t → ElU b t → ElU a t → ElU b t → C

    -- The pre-patch changed a (L x) to a (L x'), through a diff d, 
    -- whereas the post patch wants to change (L z) to (R y), however, 
    -- d is not compatible with z.
    C-SetL : {n : ℕ}{t : Tel n}{a b : U n} → D t a → ElU a t → ElU b t → C

    -- Vice versa
    C-SetR : {n : ℕ}{t : Tel n}{a b : U n} → D t b → ElU a t → ElU b t → C

    C-mu-CpyCpy : {n : ℕ}{t : Tel n}{a : U (suc n)}(x y : ValU a t) → (x ≡ y → ⊥) → C
    C-mu-DelDel : {n : ℕ}{t : Tel n}{a : U (suc n)}(x y : ValU a t) → (x ≡ y → ⊥) → C
    C-mu-DelCpy : {n : ℕ}{t : Tel n}{a : U (suc n)}(x y : ValU a t) → (x ≡ y → ⊥) → C
    C-mu-CpyDel : {n : ℕ}{t : Tel n}{a : U (suc n)}(x y : ValU a t) → (x ≡ y → ⊥) → C
    
    C-mu-DwnCpy : {n : ℕ}{t : Tel n}{a : U (suc n)} → ValU a t → D t (β a u1) → C
    C-mu-CpyDwn : {n : ℕ}{t : Tel n}{a : U (suc n)} → ValU a t → D t (β a u1) → C

    C-mu-Empty  : C
    C-mu-DwnDel : {n : ℕ}{t : Tel n}{a : U (suc n)} → D t (β a u1) → ValU a t → C
    C-mu-DelDwn : {n : ℕ}{t : Tel n}{a : U (suc n)} → D t (β a u1) → ValU a t → C

    C-Pair : C → C → C

\end{code}
%</C-def>

A simple applicative style application combinator.

%<*conflict-app>
\begin{code}
  _<C>_ : {A B : Set} → (A → B) → A ⊎ C → B ⊎ C
  f <C> i1 x = i1 (f x)
  f <C> i2 y = i2 y
\end{code}
%</conflict-app>

Finally, the actual residual definition.

%<*residual-type>
\begin{code}
  mutual
    {-# TERMINATING #-}
    _/_ : {n : ℕ}{t : Tel n}{ty : U n} 
        → D t ty → D t ty → D t ty ⊎ C
\end{code}
%</residual-type>
\begin{code}
    _/_ p D-id = i1 p
    _/_ D-id _ = i1 D-id

    _/_ {ty = u1} p q = i1 D-void

    _/_ {ty = a ⊕ b} (D-inl p) (D-inl q) = D-inl <C> (p / q)
    _/_ {ty = a ⊕ b} (D-inl p) (D-inr q) = i2 (C-LR p q)
    _/_ {ty = a ⊕ b} (D-inr p) (D-inl q) = i2 (C-LR q p)
    _/_ {ty = a ⊕ b} (D-inr p) (D-inr q) = D-inr <C> (p / q)
    
    _/_ {ty = a ⊕ b} (D-set xa xb) (D-set ya yb) with xa ≟-U ya | xb ≟-U yb
    ...| yes _ | yes _ = i1 (D-set xa xb)
    ...| _ | _ = i2 (C-SetSet xa xb ya yb)  
     
    _/_ {ty = a ⊕ b} p (D-set x y) = i1 p
    _/_ {ty = a ⊕ b} (D-set x y) (D-inl q) = i2 (C-SetL q x y)
    _/_ {ty = a ⊕ b} (D-set x y) (D-inr q) = i2 (C-SetR q x y)

    _/_ {ty = a ⊗ b} (D-pair p1 p2) (D-pair q1 q2)
      with p1 / q1 | p2 / q2
    ...| i1 pr | i1 qr = i1 (D-pair pr qr)
    ...| i1 _  | i2 c  = i2 c
    ...| i2 c  | i1 _  = i2 c
    ...| i2 c  | i2 c2 = i2 (C-Pair c c2)

    _/_ {ty = β F x} (D-β p) (D-β q) = D-β <C> (p / q)
    _/_ {ty = vl} (D-top p) (D-top q) = D-top <C> (p / q)
    _/_ {ty = wk ty} (D-pop p) (D-pop q) = D-pop <C> (p / q)

    _/_ {ty = μ ty} (D-mu p) (D-mu q) = D-mu <C> res p q

    res : {n : ℕ}{t : Tel n}{ty : U (suc n)}
        → List (Dμ t ty) → List (Dμ t ty) → List (Dμ t ty) ⊎ C

    -- if both patches finishes together, easy.
    res [] [] = i1 []
   
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
    ...| no  p = i2 (C-mu-CpyCpy x y p) 

    -- Erasing is a bit more tricky.
    res (Dμ-del x ∷ dp) (Dμ-cpy y ∷ dq) with x ≟-U y
    ...| yes _ = _∷_ (Dμ-del x) <C> res dp dq
    ...| no  p = i2 (C-mu-DelCpy x y p)
    res (Dμ-cpy x ∷ dp) (Dμ-del y ∷ dq) with x ≟-U y
    ...| yes _ = res dp dq
    ...| no  p = i2 (C-mu-CpyDel x y p)
    res (Dμ-del x ∷ dp) (Dμ-del y ∷ dq) with x ≟-U y
    ...| yes _ = res dp dq
    ...| no  p = i2 (C-mu-DelDel x y p)

    res (Dμ-dwn dx ∷ dp) (Dμ-cpy y ∷ dq) with gapply dx (red y)
    ...| just  _ = _∷_ (Dμ-dwn dx) <C> res dp dq
    ...| nothing = i2 (C-mu-DwnCpy y dx) 
    res (Dμ-cpy x ∷ dp) (Dμ-dwn dy ∷ dq) with gapply dy (red x)
    ...| just (red x2) = _∷_ (Dμ-cpy x2) <C> res dp dq
    ...| nothing       = i2 (C-mu-CpyDwn x dy)
    res (Dμ-dwn dx ∷ dp) (Dμ-dwn dy ∷ dq) with dx / dy
    ...| i1 x2  = _∷_ (Dμ-dwn x2) <C> res dp dq
    ...| i2 c   = i2 c

    res (Dμ-dwn dx ∷ dp) (Dμ-del y ∷ dq) = i2 (C-mu-DwnDel dx y)
    res (Dμ-del y ∷ dp) (Dμ-dwn dx ∷ dq) = i2 (C-mu-DelDwn dx y)
    res [] _  = i2 C-mu-Empty
    res _ []  = i2 C-mu-Empty

\end{code}

%<*NoConflict>
\begin{code}
  NoConflict : ∀{a}{A : Set a} → A ⊎ C → Set
  NoConflict (i1 _) = Unit
  NoConflict (i2 _) = ⊥
\end{code}
%</NoConflict>


%<*merge>
\begin{code}
  merge : {n : ℕ}{t : Tel n}{ty : U n}
        → D t ty → D t ty → (D t ty × D t ty) ⊎ C
  merge d1 d2 with d1 / d2
  ...| i2 c = i2 c
  ...| i1 d12 with d2 / d1
  ...| i2 c = i2 c
  ...| i1 d21 = i1 (d21 , d12)
\end{code}
%</merge>

%<*merge-compare>
\begin{code}
  merge-cmp : {n : ℕ}{t : Tel n}{ty : U n}
            → (e1 e2 e3 : ElU ty t) → (D t ty ⊎ Bool) ⊎ C
  merge-cmp e1 e2 e3 with gdiff e1 e2 | gdiff e1 e3
  ...| d12 | d13 with merge d12 d13
  ...| i2 c = i2 c
  ...| i1 (d123 , d132) with gapply d123 e2 | gapply d132 e3
  ...| nothing | just _ = i1 (i2 false)
  ...| just _ | nothing = i1 (i2 false)
  ...| nothing | nothing = i1 (i2 false)
  ...| just d42 | just d43 with d42 ≟-U d43
  ...| yes _ = i1 (i2 true)
  ...| no  _ = i1 (i1 (gdiff d42 d43))
\end{code}
%</merge-compare>
