\begin{code}
open import Prelude
open import Prelude.ListProperties using (All; all?)
open import Prelude.Monad
open import Diffing.CF-base
open import CF.Operations.Derivative

open import Diffing.Patches.D
open import Diffing.Patches.Conflicts

module Diffing.Patches.Residual where

  open Monad {{...}}
\end{code}

\begin{code}
  select : {A : Set} → ℕ → List A → Maybe A
  select n [] = nothing
  select zero    (x ∷ as) = just x
  select (suc n) (x ∷ as) = select n as
\end{code}

\begin{code}
  {-# TERMINATING #-}
  res : {n : ℕ}{t : T n}{ty : U n}
      → (p q : Patch ty t)
      → Maybe (D C ty t)
  res (D-A ()) q
  res p (D-A ())
  res D-unit D-unit = just D-unit
  
  res (D-inl p) (D-inl q) = D-inl <M> res p q
  res (D-inl p) (D-setl x y)
    with D-is-id? p
  ...| yes _ = just (D-setl x y)
  ...| no  _ = (D-A ∘ (λ z → UU (inl x) (inl z) (inr y))) <M> D-dst p
  res (D-inr p) (D-inr q) = D-inr <M> res p q
  res (D-inr p) (D-setr x y)
    with D-is-id? p
  ...| yes _ = just (D-setr x y)
  ...| no  _ = (D-A ∘ (λ z → UU (inr x) (inr z) (inl y))) <M> D-dst p
  res (D-setl x y) (D-setl w z)
    with x ≟-U w | y ≟-U z
  ...| yes xw | yes yz = just (gdiff-id (inr z))
  ...| no _   | _      = nothing
  ...| yes xw | no ¬yz = just (D-A (UU (inl x) (inr y) (inr z)))
  res (D-setr x y) (D-inr q)
    with D-is-id? q
  ...| yes _ = just (D-setr x y)
  ...| no  _ = (D-A ∘ (λ z → UU (inr x) (inl y) (inr z))) <M> D-dst q
  res (D-setr x y) (D-setr w z)
    with x ≟-U w | y ≟-U z
  ...| yes xw | yes yz = just (gdiff-id (inl z))
  ...| no _   | _      = nothing
  ...| yes xw | no ¬yz = just (D-A (UU (inr x) (inl y) (inl z)))
  res (D-setl x y) (D-inl q)
    with D-is-id? q
  ...| yes _ = just (D-setl x y)
  ...| no  _ = (D-A ∘ (λ z → UU (inl x) (inr y) (inl z))) <M> D-dst q
  res (D-inr p) (D-inl q) = nothing
  res (D-inl p) (D-inr q) = nothing
  res (D-inl p) (D-setr x x₁) = nothing
  res (D-inr p) (D-setl x x₁) = nothing
  res (D-setl x x₁) (D-inr q) = nothing
  res (D-setl x x₁) (D-setr x₂ x₃) = nothing
  res (D-setr x x₁) (D-inl q) = nothing
  res (D-setr x x₁) (D-setl x₂ x₃) = nothing
  
  res (D-pair p p₁) (D-pair q q₁)
    = D-pair <M> res p q <M*> res p₁ q₁
  
  res (D-def p) (D-def q) = D-def <M> res p q
  res (D-top p) (D-top q) = D-top <M> res p q
  res (D-pop p) (D-pop q) = D-pop <M> res p q

  res (D-μ-add ctx p) (D-μ-add dtx q)
    = (D-A ∘ GLR ctx dtx) <M> res p q
  res (D-μ-add ctx p) q
    = (D-A ∘ GL ctx) <M> res p q
  res p (D-μ-add ctx q)
    = (D-A ∘ GR ctx) <M> res p q
    
  -- assumes length ps ≡ length qs ≡ ar (D-src p) ≡ ar (D-dst q) ≡ ..
  res (D-μ-dwn p ps) (D-μ-dwn q qs)
    = D-μ-dwn <M> res p q <M*> zipWithM res ps qs

  -- Assumes length ps ≡ suc (φ-ar 0 ctx)
  res (D-μ-dwn p ps) (D-μ-rmv ctx q)
    with D-dst (D-μ-dwn p ps)
  ...| nothing = nothing
  ...| just (mu x) with match ctx x
  ...| nothing = (D-A ∘ UD ctx (mu x)) <M> (select (Zidx ctx) ps >>= flip res q)
  ...| just x' = select (Zidx ctx) ps >>= flip res q


  res (D-μ-rmv ctx p) (D-μ-dwn q qs)
    with D-dst (D-μ-dwn q qs)
  ...| nothing = nothing
  ...| just (mu x) with match ctx x
  ...| nothing = (D-A ∘ DU ctx (mu x)) <M> (select (Zidx ctx) qs >>= res p)
  ...| just x' = D-μ-rmv ctx <M> (select (Zidx ctx) qs >>= res p)
  
  res (D-μ-rmv ctx p) (D-μ-rmv dtx q)
    with ctx ≟-Ctx dtx
  ...| yes pq = res p q
  ...| no ¬pq = (D-A ∘ DD ctx dtx) <M> res p q
\end{code}
