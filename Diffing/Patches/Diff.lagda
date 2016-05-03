\begin{code}
open import Prelude
open import Prelude.Vector
open import CF
open import CF.Derivative.Operations
open import CF.Operations.Properties
  using (ch-v)

open import Diffing.Patches.D
open import Diffing.Patches.Cost

module Diffing.Patches.Diff (Δ : Cost) where
  open Cost
  
  infixr 20 _⊓_
\end{code}

  Another way of writing the type of gdiff
  could be:

  gdiff : ElU × ElU ⇒ Patch

%<*gdiff-type>
\begin{code}
  gdiff-μ : {n : ℕ}{t : T n}{ty : U (suc n)} 
          → ElU (μ ty) t → ElU (μ ty) t → Patch (μ ty) t

  {-# TERMINATING #-}
  gdiff : {n : ℕ}{t : T n}{ty : U n} 
        → ElU ty t → ElU ty t → Patch ty t
\end{code}
%</gdiff-type>

%<*cost-def>
\begin{code}
  cost : {n : ℕ}{t : T n}{ty : U n} → Patch ty t → ℕ
  cost (D-A ())
  cost D-unit         = 0
  cost (D-inl d)      = cost d
  cost (D-inr d)      = cost d
  cost (D-setl xa xb) = 1 + c⊕ Δ xa xb
  cost (D-setr xa xb) = 1 + c⊕ Δ xb xa
  cost (D-pair da db) = cost da + cost db
  cost (D-def d) = cost d
  cost (D-top d) = cost d
  cost (D-pop d) = cost d
  cost (D-μ-add ctx d) = cμ Δ ctx + cost d
  cost (D-μ-rmv ctx d) = cμ Δ ctx + cost d
  cost (D-μ-dwn x y hip d)
    = cost (gdiff x y) + vsum (vmap cost d)
    where
      vsum : {k : ℕ} → Vec ℕ k → ℕ
      vsum []       = 0
      vsum (x ∷ xs) = x + vsum xs
\end{code}
%</cost-def>

%<*lub-def>
\begin{code}
  _⊓_ : {n : ℕ}{t : T n}{ty : U n}
      → Patch ty t → Patch ty t → Patch ty t
  _⊓_ {ty = ty} da db with cost da ≤?-ℕ cost db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lub-def>

%<*lub-def>
\begin{code}
  postulate
    impossible : {n : ℕ}{t : T n}{ty : U n} → Patch ty t

  ⊓* : {n : ℕ}{t : T n}{ty : U n}
      → (l : List (Patch ty t)) → ∃ (λ n → suc n ≡ length l) → Patch ty t
  ⊓* [] (len , ())
  ⊓* (x ∷ []) (.0 , refl)        = x
  ⊓* (x ∷ y ∷ l) (zero , ())
  ⊓* (x ∷ y ∷ l) (suc len , prf) = x ⊓ (⊓* (y ∷ l) (len , suc-inj prf))
\end{code}
%</lub-def>

%<*gdiff-def>
\begin{code}
  gdiff {ty = var} (top a) (top b)
    = D-top (gdiff a b)
  gdiff {ty = wk u} (pop a) (pop b)
    = D-pop (gdiff a b)
  gdiff {ty = def F x} (red a) (red b)
    = D-def (gdiff a b)
  gdiff {ty = u1} unit unit
    = D-unit
  gdiff {ty = ty ⊗ tv} (ay , av) (by , bv) 
    = D-pair (gdiff ay by) (gdiff av bv)
  gdiff {ty = ty ⊕ tv} (inl ay) (inl by)
    = D-inl (gdiff ay by)
  gdiff {ty = ty ⊕ tv} (inr av) (inr bv)
    = D-inr (gdiff av bv)
  gdiff {ty = ty ⊕ tv} (inl ay) (inr bv)
    = D-setl ay bv
  gdiff {ty = ty ⊕ tv} (inr av) (inl by)
    = D-setr av by
  gdiff {ty = μ ty} a b = gdiff-μ a b
\end{code}
%</gdiff-def>
\begin{code}
  gdiff-μ-rmv gdiff-μ-add
    : {n : ℕ}{t : T n}{ty : U (suc n)} 
    → ElU (μ ty) t → ElU (μ ty) t
    → List (Patch (μ ty) t)

  gdiff-μ-dwn
    : {n : ℕ}{t : T n}{ty : U (suc n)} 
    → (a b : ElU (μ ty) t) → μ-ar a ≡ μ-ar b
    → Patch (μ ty) t

  gdiff-μ-rmv (mu a) b
    = map (λ { (ctx , pop a')
             → D-μ-rmv ctx (gdiff a' b)
             }) (zippers 0 a)

  gdiff-μ-add a (mu b)
    = map (λ { (ctx , pop b')
             → D-μ-add ctx (gdiff a b')
             }) (zippers 0 b)

  gdiff-μ-dwn (mu a) (mu b) hip
    = D-μ-dwn (fgt 0 a) (fgt 0 b) hip 
              (vmap (λ { (pop x , pop y) → gdiff x y })
                    (vzip hip (ch-v 0 a) (ch-v 0 b)))
  
\end{code}
\begin{code}
  ctx-μ-add-rmv-nonempty
    : {n : ℕ}{t : T n}{ty : U (suc n)}
    → (a b : ElU (μ ty) t)(hip : μ-ar a ≡ μ-ar b → ⊥)
    → ∃ (λ n → suc n ≡ length (gdiff-μ-add a b ++ gdiff-μ-rmv a b))
  ctx-μ-add-rmv-nonempty a b hip = {!!}
\end{code}
%<*gdiff-mu-def>
\begin{code}
  gdiff-μ a b with μ-ar a ≟-ℕ μ-ar b
  ...| no  p
     = ⊓* (gdiff-μ-add a b ++ gdiff-μ-rmv a b)
          {!!}
  ...| yes p
     = ⊓* (gdiff-μ-dwn a b p ∷ gdiff-μ-add a b
          ++ gdiff-μ-rmv a b)
          (length (gdiff-μ-add a b ++ gdiff-μ-rmv a b) , refl)
\end{code}
%</gdiff-mu-def>
