\begin{code}
open import Prelude
open import Diffing.CF-base
open import Diffing.Patches.D

module Diffing.Patches.Conflicts where
\end{code}

\begin{code}
  data C : {n : ℕ} → U n → T n → Set where
    UU : {n : ℕ}{t : T n}{a b : U n}
       → (x y z : ElU (a ⊕ b) t) → C (a ⊕ b) t
    DU UD : {n : ℕ}{t : T n}{ty : U (suc n)}
       → Ctx 0 ty (μ ty ∷ t) → ElU (μ ty) t → C (μ ty) t
    GL GR : {n : ℕ}{t : T n}{ty : U (suc n)}
       → Ctx 0 ty (μ ty ∷ t) → C (μ ty) t
    GLR DD : {n : ℕ}{t : T n}{ty : U (suc n)}
       → (p q : Ctx 0 ty (μ ty ∷ t)) → C (μ ty) t
\end{code}

\begin{code}
  C-sym : {n : ℕ}{t : T n}{ty : U n}
        → C ty t → C ty t
  C-sym (UU x y z) = UU x z y
  C-sym (DU x x₁) = UD x x₁
  C-sym (UD x x₁) = DU x x₁
  C-sym (GL x) = GR x
  C-sym (GR x) = GL x
  C-sym (GLR p q) = GLR q p
  C-sym (DD p q) = DD q p
\end{code}
