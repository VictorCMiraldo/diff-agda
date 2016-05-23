\begin{code}
open import Prelude
open import Prelude.Vector
open import Prelude.Monad

open import Diffing.CF-base
open import CF.Derivative
  using (match; _◂_)
open import CF.Properties.Derivative
  using (match-correct)
open import Diffing.Patches.D

module Diffing.Patches.Apply where

  open Monad {{...}}
\end{code}

\begin{code}
  {-# TERMINATING #-}
  gapply : {n : ℕ}{t : T n}{ty : U n}
         → (p : Patch ty t)(x : ElU ty t)
         → Maybe (ElU ty t)
\end{code}
\begin{code}
  gapply (D-A ()) x
  gapply D-unit unit = just unit
  gapply (D-inl p) (inl x) = inl <M> gapply p x
  gapply (D-inl p) (inr x) = nothing
  gapply (D-inr p) (inl x) = nothing
  gapply (D-inr p) (inr x) = inr <M> gapply p x
  gapply (D-setl p q) (inl x)
    with p ≟-U x
  ...| yes r = just (inr q)
  ...| no  r = nothing
  gapply (D-setl p q) (inr x) = nothing
  gapply (D-setr p q) (inl x) = nothing
  gapply (D-setr p q) (inr x)
    with p ≟-U x
  ...| yes r = just (inl q)
  ...| no  r = nothing
  gapply (D-pair p q) (x , y)
    = _,_ <M> gapply p x <M*> gapply q y
  gapply (D-def p) (red x) = red <M> gapply p x
  gapply (D-top p) (top x) = top <M> gapply p x
  gapply (D-pop p) (pop x) = pop <M> gapply p x
  gapply (D-μ-add ctx p) x
    = (mu ∘ _◂_ ctx ∘ pop) <M>  gapply p x
  gapply (D-μ-rmv ctx p) (mu x)
    with match ctx x
  ...| nothing = nothing
  ...| just (pop x') = gapply p x'
  gapply (D-μ-dwn px p) (mu x)
    with gapply px (fgt 0 x)
  ...| nothing = nothing
  ...| just x'
     = mu <M> join (plug 0 x' <M> zipWithM gapply (map D-pop p) (ch 0 x))
\end{code}

\begin{code}
  gapply-correct
    : {n : ℕ}{t : T n}{ty : U n}
    → (x y : ElU ty t)(p : Patch ty t)
    → [ x , y ]⇒ p
    → gapply p x ≡ just y
  gapply-correct x y (D-A ()) hip
  gapply-correct unit unit D-unit hip = refl
  gapply-correct (inl x) (inl y) (D-inl p) hip = {!!}
  gapply-correct (inl x) (inr y) (D-inl p) (_ , q) = {!!}
  gapply-correct (inr x) (inl y) (D-inl p) hip = {!!}
  gapply-correct (inr x) (inr y) (D-inl p) hip = {!!}
  gapply-correct x y (D-inr p) hip = {!!}
  gapply-correct x y (D-setl x₁ x₂) hip = {!!}
  gapply-correct x y (D-setr x₁ x₂) hip = {!!}
  gapply-correct x y (D-pair p p₁) hip = {!!}
  gapply-correct x₁ y (D-def p) hip = {!!}
  gapply-correct x y (D-top p) hip = {!!}
  gapply-correct x y (D-pop p) hip = {!!}
  gapply-correct (mu x) (mu y) (D-μ-dwn px p) (h0 , h1)
    with <M>-elim h0 | <M>-elim h1
  ...| .x , refl , s0 | .y , refl , s1
    = {!!}
  gapply-correct x y (D-μ-add ctx p) (h0 , h1)
    with <M>-elim h1
  ...| q , r , s rewrite gapply-correct x q p (h0 , s)
     = cong just (sym r)
  gapply-correct (mu x) y (D-μ-rmv ctx p) (h0 , h1)
    with <M>-elim h0
  ...| q , r , s
    rewrite inj-mu r
     | match-correct ctx (pop q)
     = gapply-correct q y p (s , h1)
\end{code}
