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
       → Ctx 0 ty (μ ty ∷ t) → ElU (μ ty) t → D C (μ ty) t → C (μ ty) t
    GL GR : {n : ℕ}{t : T n}{ty : U (suc n)}
       → Ctx 0 ty (μ ty ∷ t) → D C (μ ty) t → C (μ ty) t
    GLR DD : {n : ℕ}{t : T n}{ty : U (suc n)}
       → (p q : Ctx 0 ty (μ ty ∷ t)) → D C (μ ty) t → C (μ ty) t
\end{code}
