\begin{code}
open import Prelude
open import Prelude.Monad
open import Diffing.CF-base
open import Diffing.Patches.D
open import Diffing.Patches.Conflicts

module Diffing.Patches.Residual where
\end{code}

\begin{code}
  _∥_ : {n : ℕ}{t : T n}{ty : U n}
      → (p q : Patch ty t)
      → Set
  p ∥ q = Is-Just (D-src p) × D-src p ≡ D-src q
\end{code}

\begin{code}
  focus : {n i : ℕ}{t : T n}{ty : U n}
        → Ctx i ty t → ℕ
  focus φ-hole = 0
  focus (φ-left ctx) = focus ctx
  focus (φ-right ctx) = focus ctx
  focus (φ-fst x ctx) = focus ctx
  focus {i = i} (φ-snd x ctx) = ar i x + focus ctx
  focus (φ-pop ctx) = focus ctx
  focus (φ-defhd ctx) = focus ctx
  focus (φ-deftl ctx ctx₁) = φ-ar 0 ctx + focus ctx₁
  focus (φ-muhd ctx) = focus ctx
  focus (φ-mutl ctx ctx₁) = φ-ar 0 ctx + focus ctx₁
\end{code}

\begin{code}
  {-# TERMINATING #-}
  res : {n : ℕ}{t : T n}{ty : U n}
      → (p q : Patch ty t)
      → Maybe (D C ty t)
  res (D-A ()) q
  res p (D-A ())
  res D-unit D-unit = just D-unit
  
  res (D-inl p) (D-inl q) = {!!}
  res (D-inl p) (D-setl x y) = {!!}
  res (D-inr p) (D-inr q) = {!!}
  res (D-inr p) (D-setr x y) = {!!}
  res (D-setl x y) (D-setl w z) = {!!}
  res (D-setr x y) (D-inr q) = {!!}
  res (D-setr x y) (D-setr w z) = {!!}
  res (D-setl x y) (D-inl q) = {!!}
  res (D-inr p) (D-inl q) = {!!}
  res (D-inl p) (D-inr q) = {!!}
  res (D-inl p) (D-setr x x₁) = {!!}
  res (D-inr p) (D-setl x x₁) = {!!}
  res (D-setl x x₁) (D-inr q) = {!!}
  res (D-setl x x₁) (D-setr x₂ x₃) = {!!}
  res (D-setr x x₁) (D-inl q) = {!!}
  res (D-setr x x₁) (D-setl x₂ x₃) = {!!}
  
  res (D-pair p p₁) (D-pair q q₁) = {!!}
  
  res (D-def p) (D-def q) = D-def <M> res p q
  res (D-top p) (D-top q) = D-top <M> res p q
  res (D-pop p) (D-pop q) = D-pop <M> res p q

  res (D-μ-add ctx p) (D-μ-add dtx q)
    = (D-A ∘ GLR ctx dtx) <M> res p q
  res (D-μ-add ctx p) q
    = (D-A ∘ GL ctx) <M> res p q
  res p (D-μ-add ctx q)
    = (D-A ∘ GR ctx) <M> res p q
  
  res (D-μ-dwn p ps) (D-μ-dwn q qs)
    = D-μ-dwn <M> res p q <M*> zipWithM res ps qs
  res (D-μ-dwn p ps) (D-μ-rmv ctx q) = {!!}
  res (D-μ-rmv ctx p) (D-μ-dwn q qs) = {!!}
  res (D-μ-rmv ctx p) (D-μ-rmv dtx q) = {!!}
\end{code}
