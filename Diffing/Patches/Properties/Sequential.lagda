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
    ⟶-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
      → {p q : D A t ty} → (p ⟶ q)
      → (WF p × WF q) × D-dst p ≡ D-src q
    ⟶-elim hip = hip
\end{code}

\begin{code}
    ⟶-inl : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
          → (p q : D A t ty)
          → (D-inl {b = tv} p) ⟶ D-inl q
          → p ⟶ q
    ⟶-inl p q ((wp , wq) , prf)
      = (D-inl-wf p wp , D-inl-wf q wq) , <M>-inj inj-inl prf

  postulate
    ⟶-inl-inr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t ty)(q : D A t tv)
      → (D-inl p) ⟶ (D-inr q)
      → ⊥

    ⟶-inl-setr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t ty)(x : ElU tv t)(y : ElU ty t)
      → (D-inl p) ⟶ (D-setr x y)
      → ⊥
\end{code}
