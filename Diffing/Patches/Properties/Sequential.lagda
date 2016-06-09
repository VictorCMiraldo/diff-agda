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

    ⟶-inr : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
          → (p q : D A t tv)
          → (D-inr {a = ty} p) ⟶ D-inr q
          → p ⟶ q
    ⟶-inr p q ((wp , wq) , prf)
      = (D-inr-wf p wp , D-inr-wf q wq) , <M>-inj inj-inr prf

    ⟶-inl-inr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t ty)(q : D A t tv)
      → (D-inl p) ⟶ (D-inr q)
      → ⊥
    ⟶-inl-inr-⊥ p q ((((sp , dp) , hsp , hdp) , ((sq , dq) , hsq , hdq)) , hip)
      with <M>-elim hdp | <M>-elim hsq
    ...| r0 , r1 , r2 | s0 , s1 , s2
      rewrite r2 | s2 = inl≡inr→⊥ (just-inj hip)

    ⟶-inr-inl-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t tv)(q : D A t ty)
      → (D-inr p) ⟶ (D-inl q)
      → ⊥
    ⟶-inr-inl-⊥ p q ((((sp , dp) , hsp , hdp) , ((sq , dq) , hsq , hdq)) , hip)
      with <M>-elim hdp | <M>-elim hsq
    ...| r0 , r1 , r2 | s0 , s1 , s2
      rewrite r2 | s2 = inl≡inr→⊥ (just-inj (sym hip))

    ⟶-inl-setr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t ty)(x : ElU tv t)(y : ElU ty t)
      → (D-inl p) ⟶ (D-setr x y)
      → ⊥
    ⟶-inl-setr-⊥ p x y (wpq , hip)
      with <M>-elim hip
    ...| r0 , r1 , r2 = inl≡inr→⊥ (sym r1)

    ⟶-inr-setl-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t tv)(x : ElU ty t)(y : ElU tv t)
      → (D-inr p) ⟶ (D-setl x y)
      → ⊥
    ⟶-inr-setl-⊥ p x y (wpq , hip)
      with <M>-elim hip
    ...| r0 , r1 , r2 = inl≡inr→⊥ r1

    ⟶-setl-inl-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t ty)(x : ElU ty t)(y : ElU tv t)
      → (D-setl x y) ⟶ (D-inl p)
      → ⊥
    ⟶-setl-inl-⊥ p x y (wpq , hip)
      with <M>-elim (sym hip)
    ...| r0 , r1 , r2 = inl≡inr→⊥ (sym r1)

    ⟶-setr-inr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t tv)(x : ElU tv t)(y : ElU ty t)
      → (D-setr x y) ⟶ (D-inr p)
      → ⊥
    ⟶-setr-inr-⊥ p x y (wpq , hip)
      with <M>-elim (sym hip)
    ...| r0 , r1 , r2 = inl≡inr→⊥ r1

    ⟶-setl-setl-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (x0 x1 : ElU tv t)(y0 y1 : ElU ty t)
      → (D-setl {A = A} x0 y0) ⟶ (D-setl x1 y1)
      → ⊥
    ⟶-setl-setl-⊥ x0 x1 y0 y1 (wpq , hip)
      = inl≡inr→⊥ (just-inj (sym hip))

    ⟶-setr-setr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (x0 x1 : ElU ty t)(y0 y1 : ElU tv t)
      → (D-setr {A = A} x0 y0) ⟶ (D-setr x1 y1)
      → ⊥
    ⟶-setr-setr-⊥ x0 x1 y0 y1 (wpq , hip)
      = inl≡inr→⊥ (just-inj hip)

    ⟶-def : {A : TU→Set}{n : ℕ}{t : T n}{x : U n}{F : U (suc n)}
          → (p q : D A (x ∷ t) F)
          → D-def p ⟶ D-def q
          → p ⟶ q
    ⟶-def p q ((wp , wq) , hip)
      = (D-def-wf p wp , D-def-wf q wq) , <M>-inj inj-red hip

    ⟶-top : {A : TU→Set}{n : ℕ}{t : T n}{x : U n}
          → (p q : D A t x)
          → D-top p ⟶ D-top q
          → p ⟶ q
    ⟶-top p q ((wp , wq) , hip)
      = (D-top-wf p wp , D-top-wf q wq) , <M>-inj inj-top hip

    ⟶-pop : {A : TU→Set}{n : ℕ}{t : T n}{a b : U n}
          → (p q : D A t b)
          → D-pop {a = a} p ⟶ D-pop q
          → p ⟶ q
    ⟶-pop p q ((wp , wq) , hip)
      = (D-pop-wf p wp , D-pop-wf q wq) , <M>-inj inj-pop hip

  postulate
    ⟶-pair
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (q0 q1 : D A t ty)(r0 r1 : D A t tv)
      → (D-pair q0 r0) ⟶ (D-pair q1 r1)
      → (q0 ⟶ q1) × (r0 ⟶ r1)
    -- ⟶-pair q0 q1 r0 r1 (wqr , hip)
      {- = let wfq0 , wfr0 = D-pair-wf q0 r0 (p1 wqr)
            wfq1 , wfr1 = D-pair-wf q1 r1 (p2 wqr)
         in ((wfq0 , wfq1) , {!!})
          , {!!}
      -}
\end{code}
