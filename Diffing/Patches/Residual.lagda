\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff
open import Diffing.Patches.Alignment

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
\end{code}
%</C-def>

A simple applicative style application combinator.

%<*conflict-app>
\begin{code}
  _<C>_ : {A B : Set} → (A → B) → A ⊎ C → B ⊎ C
  f <C> i1 x = i1 (f x)
  f <C> i2 y = i2 y

  _<C*>_ : {A B : Set} → (A → B) ⊎ C → A ⊎ C → B ⊎ C
  (i2 c) <C*> _      = i2 c
  (i1 f) <C*> (i2 c) = i2 c
  (i1 f) <C*> (i1 a) = i1 (f a)

  infixl 25 _<C*>_
  infixl 25 _<C>_
\end{code}
%</conflict-app>

%<*residual-type>
\begin{code}
  _/_⊔_ : {n : ℕ}{t : Tel n}{ty : U n} 
        → (a b : D t ty) → a a⇓ b → D t ty ⊎ C
\end{code}
%</residual-type>
\begin{code}
  da / db ⊔ a = res da db a
    where 
      mutual
        res : {n : ℕ}{t : Tel n}{ty : U n} 
            → (a b : D t ty) → a a⇓ b → D t ty ⊎ C
        -- We shall hardocde the relation with identity and residuals.
        res da D-id _ = i1 da
        res D-id _  _ = i1 D-id

        res {ty = u1} da db al = i1 D-void

        -- Due to alignment, we only need to take care of
        -- half the cases for coproducts.
        -- The first cases are trivial.
        res {ty = a ⊕ b} (D-inl da) (D-inl db) (a-inl al) 
          = D-inl <C> res da db al
        res {ty = a ⊕ b} (D-inr da) (D-inr db) (a-inr al) 
          = D-inr <C> res da db al

        -- Setting things must agree to be "merged"
        res {ty = a ⊕ b} (D-setl x y) (D-setl .x z) a-setl
          with y ≟-U z
        ...| yes _ = i1 (D-setl x y)
        ...| no _  = i2 {!!}
        res {ty = a ⊕ b} (D-setr x y) (D-setr .x z) a-setr 
          with y ≟-U z
        ...| yes _ = i1 (D-setr x y)
        ...| no _  = i2 {!!}

        -- Now, the following cases can be discussed. Yet, I believe this
        -- should be a conflict as somebody changed a (i1) to a (i2),
        -- and somebody else made structural changes into this i1 or i2.
        --
        -- The obvious merging would be to try and apply the structural
        -- changes to the newly set value, however, this depends heavily
        -- on the file semantics.
        res {ty = a ⊕ b} (D-setl x y) (D-inl db) a-setinl 
          = i2 {!!}
        res {ty = a ⊕ b} (D-setr x y) (D-inr db) a-setinr 
          = i2 {!!}
        res {ty = a ⊕ b} (D-inl da) (D-setl x y) a-insetl 
          = i2 {!!}
        res {ty = a ⊕ b} (D-inr da) (D-setr x y) a-insetr 
          = i2 {!!}

        -- The rest of them are clearly out of alignment.
        res {ty = a ⊕ b} (D-inl da) (D-inr db) ()
        res {ty = a ⊕ b} (D-inl da) (D-setr x y) ()
        res {ty = a ⊕ b} (D-inr da) (D-inl db) ()
        res {ty = a ⊕ b} (D-inr da) (D-setl x y) ()
        res {ty = a ⊕ b} (D-setl x y) (D-inr db) ()
        res {ty = a ⊕ b} (D-setl x y) (D-setr w z) ()
        res {ty = a ⊕ b} (D-setr x y) (D-inl db) ()
        res {ty = a ⊕ b} (D-setr x y) (D-setl w z) ()
        
        -- Pairs are simple,
        res {ty = a ⊗ b} (D-pair da1 da2) (D-pair db1 db2) (a-pair al1 al2) 
          = D-pair <C> res da1 db1 al1 <C*> res da2 db2 al2

        -- Auxiliar constructors to handle type-variables
        -- are also trivial.
        res {ty = β F x} (D-β da) (D-β db) (a-β a) 
          = D-β <C> res da db a
        res {ty = vl} (D-top da) (D-top db) (a-top a) 
          = D-top <C> res da db a
        res {ty = wk ty} (D-pop da) (D-pop db) (a-pop a) 
          = D-pop <C> res da db a

        -- Fixed points require a helper function.
        res {ty = μ ty} (D-mu da) (D-mu db) (a-mu a*)
          = D-mu <C> res* da db a*

        res* : {n : ℕ}{t : Tel n}{ty : U (suc n)}
          → (a b : List (Dμ t ty)) → a a⇓* b → List (Dμ t ty) ⊎ C

        -- if both patches finishes together, easy.
        res* [] [] a*-nil = i1 []

        -- we can always keep inserting things, though.
        -- If we find the same exact insert, though, we simply copy it.
        res* (Dμ-ins x ∷ dp) (Dμ-ins y ∷ dq) a with x ≟-U y
        ...| yes _ = _∷_ (Dμ-cpy x) <C> res* dp dq {!!}
        ...| no  _ = _∷_ (Dμ-ins x) <C> res* dp (Dμ-ins y ∷ dq) {!!}
        res* dp (Dμ-ins x ∷ dq) a = _∷_ (Dμ-cpy x) <C> res* dp dq {!!}
        res* (Dμ-ins x ∷ dp) dq a = _∷_ (Dμ-ins x) <C> res* dp dq {!!}

        -- Copies must be consistent.
        res* (Dμ-cpy x ∷ dp) (Dμ-cpy y ∷ dq) a with x ≟-U y
        ...| yes _ = _∷_ (Dμ-cpy x) <C> res* dp dq {!!}
        ...| no  p = i2 {!!} 

        -- Erasing is a bit more tricky.
        res* (Dμ-del x ∷ dp) (Dμ-cpy y ∷ dq) a with x ≟-U y
        ...| yes _ = _∷_ (Dμ-del x) <C> res* dp dq {!!}
        ...| no  p = i2 {!!}
        res* (Dμ-cpy x ∷ dp) (Dμ-del y ∷ dq) a with x ≟-U y
        ...| yes _ = res* dp dq {!!}
        ...| no  p = i2 {!!}
        res* (Dμ-del x ∷ dp) (Dμ-del y ∷ dq) a with x ≟-U y
        ...| yes _ = res* dp dq {!!}
        ...| no  p = i2 {!!}

        res* (Dμ-dwn dx ∷ dp) (Dμ-cpy y ∷ dq) a with gapply dx (red y)
        ...| just  _ = _∷_ (Dμ-dwn dx) <C> res* dp dq {!!}
        ...| nothing = i2 {!!} 
        res* (Dμ-cpy x ∷ dp) (Dμ-dwn dy ∷ dq) a with gapply dy (red x)
        ...| just (red x2) = _∷_ (Dμ-cpy x2) <C> res* dp dq {!!}
        ...| nothing       = i2 {!!}
        res* (Dμ-dwn dx ∷ dp) (Dμ-dwn dy ∷ dq) (a*-tail a) with res dx dy {!a!}
        ...| i1 x2  = _∷_ (Dμ-dwn x2) <C> res* dp dq {!!}
        ...| i2 c   = i2 c
        res* (Dμ-dwn dx ∷ dp) (Dμ-dwn dy ∷ dq) (a*-dwn a as) with res dx dy {!a!}
        ...| i1 x2  = _∷_ (Dμ-dwn x2) <C> res* dp dq {!!}
        ...| i2 c   = i2 c

        res* (Dμ-dwn dx ∷ dp) (Dμ-del y ∷ dq) a = i2 {!!}
        res* (Dμ-del y ∷ dp) (Dμ-dwn dx ∷ dq) a = i2 {!!}
        res* [] _ a = i2 {!!}
        res* _ [] a = i2 {!!}
\end{code}
