\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Utils.Vector
open import Diffing.Patches.Diff.D
open import Diffing.Patches.Diff.Cost

module Diffing.Patches.Diff.E (Δ : Cost) where

  open import Diffing.Patches.Diff Δ
\end{code}

\begin{code}
  data E {a}(A : {n : ℕ} → T n → U n → Set a) 
      : {n : ℕ} → T n → U n → Set a where
    E-A    : {n : ℕ}{t : T n}{ty : U n} → A t ty → E A t ty
    E-unit : {n : ℕ}{t : T n} → E A t u1
    E-inl  : {n : ℕ}{t : T n}{a b : U n} 
           → E A t a → E A t (a ⊕ b)
    E-inr  : {n : ℕ}{t : T n}{a b : U n} 
           → E A t b → E A t (a ⊕ b)
    E-setl  : {n : ℕ}{t : T n}{a b : U n} 
            → ElU a t → ElU b t → E A t (a ⊕ b)
    E-setr  : {n : ℕ}{t : T n}{a b : U n} 
            → ElU b t → ElU a t → E A t (a ⊕ b)
    E-pair : {n : ℕ}{t : T n}{a b : U n} 
           → E A t a → E A t b → E A t (a ⊗ b)
    E-def : {n : ℕ}{t : T n}{F : U (suc n)}{x : U n} 
          → E A (x ∷ t) F → E A t (def F x)
    E-top : {n : ℕ}{t : T n}{a : U n}
          → E A t a → E A (a ∷ t) var
    E-pop : {n : ℕ}{t : T n}{a b : U n}
          → E A t b → E A (a ∷ t) (wk b)

    Eμ-end : {n : ℕ}{t : T n}{a : U (suc n)}
           → E A t (μ a)
    Eμ-ins : {n : ℕ}{t : T n}{a : U (suc n)}
           → (ea : ValU a t) → Vec (E A t (μ a)) (ar 0 ea)
           → E A t (μ a)
    Eμ-sub : {n j : ℕ}{t : T n}{a : U (suc n)}
           → {!!} 
           → E A t (μ a)
    Eμ-dwn : {n : ℕ}{t : T n}{a : U (suc n)}
           → (ea : ValU a t)(d : E A (u1 ∷ t) a) 
           → Vec (E A t (μ a)) (ar 0 ea)
           → E A t (μ a)
\end{code}

\begin{code}
  _^_ : {n : ℕ}(ty : U n) → ℕ → U n
  ty ^ zero  = u1
  ty ^ suc n = ty ⊗ (ty ^ n)
\end{code}

\begin{code}
  D→E : {n : ℕ}{t : T n}{ty : U n}
      → D ⊥ₚ t ty → E ⊥ₚ t ty

  Dμ→E : {n i j : ℕ}{t : T n}{ty : U (suc n)}
       → Dμ ⊥ₚ t ty i j → Vec (ElU (μ ty) t) i
       → E ⊥ₚ t (μ ty)
  Dμ→E (Dμ-A () d) xs
  Dμ→E Dμ-end [] = {!!}
  Dμ→E (Dμ-dwn a b d) (x ∷ xs) = {!!}
  Dμ→E (Dμ-del a d) (x ∷ xs) = {!!}
  Dμ→E (Dμ-ins a d) xs
    = Eμ-ins a {!!}

  D→E d = {!!}
\end{code}
