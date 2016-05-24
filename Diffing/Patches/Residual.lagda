\begin{code}
open import Prelude
open import Prelude.Vector
open import Diffing.CF-base
open import Diffing.Patches.D

module Diffing.Patches.Residual where
\end{code}

\begin{code}
  data C : {n : ℕ} → U n → T n → Set where
    UU : {n : ℕ}{t : T n}{a b : U n}
       → ElU (a ⊕ b) t → ElU (a ⊕ b) t → ElU (a ⊕ b) t → C (a ⊕ b) t
    DU : {n : ℕ}{t : T n}{ty : U (suc n)}
       → C (μ ty) t
    GL GR : {n : ℕ}{t : T n}{ty : U (suc n)}
       → Ctx 0 ty (μ ty ∷ t) → D C (μ ty) t → C (μ ty) t
    GLR : {n : ℕ}{t : T n}{ty : U (suc n)}
       → Ctx 0 ty (μ ty ∷ t) → Ctx 0 ty (μ ty ∷ t) → D C (μ ty) t → C (μ ty) t
\end{code}

\begin{code}
  res : {n : ℕ}{t : T n}{ty : U n}
      → (p q : Patch ty t)(hip : D-src p ≡ D-src q)
      → D C ty t
  res (D-A ()) q hip
  res p (D-A ()) hip
  res D-unit D-unit hip = D-unit
  
  res (D-inl p) (D-inl q) hip = D-inl (res p q (inj-inl hip))
  res (D-inl p) (D-setl x y) hip
    = {!!}
  res (D-inr p) (D-inr q) hip = {!!}
  res (D-inr p) (D-setr x y) hip = {!!}
  res (D-setl x y) (D-setl w z) hip = {!!}
  res (D-setr x y) (D-inr q) hip = {!!}
  res (D-setr x y) (D-setr w z) hip = {!!}
  res (D-setl x y) (D-inl q) hip = {!!}
  res (D-inr p) (D-inl q) ()
  res (D-inl p) (D-inr q) ()
  res (D-inl p) (D-setr x x₁) ()
  res (D-inr p) (D-setl x x₁) ()
  res (D-setl x x₁) (D-inr q) ()
  res (D-setl x x₁) (D-setr x₂ x₃) ()
  res (D-setr x x₁) (D-inl q) ()
  res (D-setr x x₁) (D-setl x₂ x₃) ()
  
  res (D-pair p p₁) (D-pair q q₁) hip = {!!}
  
  res (D-def p) (D-def q) hip = {!!}
  res (D-top p) (D-top q) hip = {!!}
  res (D-pop p) (D-pop q) hip = {!!}

  res (D-μ-add ctx p) (D-μ-add dtx q) hip
    = D-A (GLR ctx dtx (res p q hip))
  res (D-μ-add ctx p) q hip
    = D-A (GL ctx (res p q hip))
  res p (D-μ-add ctx q) hip
    = D-A (GR ctx (res p q hip))
  
  res (D-μ-dwn p hi ho ps) (D-μ-dwn q ii io qs) hip
    rewrite hip = D-μ-dwn (res p q {!!}) {!!} {!!} {!!}
  res (D-μ-dwn p hi ho ps) (D-μ-rmv ctx q) hip = {!!}
  res (D-μ-rmv ctx p) (D-μ-dwn q ii io qs) hip = {!!}
  res (D-μ-rmv ctx p) (D-μ-rmv dtx q) hip = {!!}
\end{code}
