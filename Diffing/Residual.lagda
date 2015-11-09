\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Diff

module Diffing.Residual where

  open import Diffing.Utils.Monads
  open Monad {{...}}
\end{code}


  Let p and q be patches for a given datatype.
  A residual (p / q) means applying p AFTER the changes by
  q have been made. 

%<*residual-type>
\begin{code}
  {-# TERMINATING #-}
  _/_ : {n : ℕ}{t : Tel n}{ty : U n} 
      → D t ty → D t ty → Maybe (D t ty)
\end{code}
%</residual-type>
  
  The first cases are the residual equalities:

    p / (q ∘ r) = (p / r) / q
    (p ∘ q) / r = p / (r / q) ∘ (q / r) 

    p / id = p
    id / p = id

  They are defined as such simply to make composite squares commute
  over residuals. 

\begin{code}
  _/_ p D-id = just p
  _/_ D-id _ = just D-id

  _/_ p (q ∘ᴰ r) = p / r >>= λ p/r → p/r / q
  _/_ (p ∘ᴰ q) r with q / r | r / q 
  ...| just q/r | just r/q = p / r/q >>= λ p/r/q → return (p/r/q ∘ᴰ q/r)
  ...| _        | _        = nothing

  _/_ {ty = u1} p q = just D-void

  _/_ {ty = a ⊕ b} (D-inl p) (D-inl q) = D-inl <$>+1 (p / q)
  _/_ {ty = a ⊕ b} (D-inl p) (D-inr q) = nothing
  _/_ {ty = a ⊕ b} (D-inr p) (D-inl q) = nothing
  _/_ {ty = a ⊕ b} (D-inr p) (D-inr q) = D-inr <$>+1 (p / q)
  _/_ {ty = a ⊕ b} p       (D-set x y) = just p
  -- TODO: how is this consistent? Maybe we'll need the
  -- previous definition of D (a ⊕ b) = D a ⊕ D b ⊕ 2 × (a , b)
  _/_ {ty = a ⊕ b} (D-set x y) (D-inl q) with gapply q x
  ...| just x2 = just (D-set x2 y)
  ...| nothing = nothing
  _/_ {ty = a ⊕ b} (D-set x y) (D-inr q) with gapply q y
  ...| just y2 = just (D-set x y2)
  ...| nothing = nothing

  _/_ {ty = a ⊗ b} (D-pair p1 p2) (D-pair q1 q2)
    with p1 / q1 | p2 / q2
  ...| just pr | just qr = just (D-pair pr qr)
  ...| _ | _ = nothing

  _/_ {ty = β F x} (D-β p) (D-β q) = D-β <$>+1 (p / q)
  _/_ {ty = vl} (D-top p) (D-top q) = D-top <$>+1 (p / q)
  _/_ {ty = wk ty} (D-pop p) (D-pop q) = D-pop <$>+1 (p / q)

  _/_ {ty = μ ty} p q = res p q
    where
      res : {n : ℕ}{t : Tel n}{ty : U (suc n)}
          → D t (μ ty) → D t (μ ty) → Maybe (D t (μ ty))

      -- if both patches finishes together, easy.
      res D-mu-end D-mu-end = just D-mu-end

      -- we can always keep inserting things, though.
      res dp (D-mu-ins x dq) = D-mu-cpy x <$>+1 res dp dq
      res (D-mu-ins x dp) dq = D-mu-ins x <$>+1 res dp dq
      
      -- Copies must be consistent.
      res (D-mu-cpy x dp) (D-mu-cpy y dq) with x ≟-U y
      ...| yes _ = D-mu-cpy x <$>+1 res dp dq
      ...| no  _ = nothing

      -- Erasing is a bit more tricky.
      res (D-mu-del x dp) (D-mu-cpy y dq) with x ≟-U y
      ...| yes _ = D-mu-del x <$>+1 res dp dq
      ...| no  _ = nothing
      res (D-mu-cpy x dp) (D-mu-del y dq) with x ≟-U y
      ...| yes _ = res dp dq
      ...| no  _ = nothing
      res (D-mu-del x dp) (D-mu-del y dq) with x ≟-U y
      ...| yes _ = res dp dq
      ...| no  _ = nothing

      res (D-mu-down dx dp) (D-mu-cpy y dq) with gapply dx (red y)
      ...| just _ = D-mu-down dx <$>+1 res dp dq
      ...| nothing = nothing
      res (D-mu-cpy x dp) (D-mu-down dy dq) with gapply dy (red x)
      ...| just (red x2) = D-mu-cpy x2 <$>+1 res dp dq
      ...| nothing       = nothing

      res _ _ = nothing    
\end{code}

  There is interest in proving
  a few lemmas:

    p / p  ≡ id
    id / p ≡ id
    p / id ≡ p
