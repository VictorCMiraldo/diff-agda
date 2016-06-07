\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Patches.D
open import Diffing.Patches.Properties.WellFounded

module Diffing.Patches.Properties.Sequential where
\end{code}

\begin{code}
  infix 30 _⟶_ _⟶μ_
  
  abstract
    _⟶_ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
        → (p q : D A t ty)
        → Set
    _⟶_ {A} {n} {t} {ty} p q
      = (WF p × WF q) × D-dst p ≡ D-src q

    _⟶μ_ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
        → (p q : List (Dμ A t ty))
        → Set
    _⟶μ_ {A} {n} {t} {ty} p q
      = (WFμ p × WFμ q) × Dμ-dst p ≡ Dμ-src q
\end{code}

\begin{code}
    ⟶-inl : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
          → (p q : D A t ty)
          → (D-inl {b = tv} p) ⟶ D-inl q
          → p ⟶ q
    ⟶-inl p q ((wp , wq) , prf)
      = (D-inl-wf p wp , D-inl-wf q wq) , <M>-inj inj-inl prf
\end{code}
