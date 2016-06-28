\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Patches.D
open import Diffing.Patches.Cost
open import Diffing.Patches.Id
open import Diffing.Patches.Inverse
open import Diffing.Patches.Composition
open import Diffing.Patches.Properties.WellFounded
open import Diffing.Patches.Properties.Alignment
open import Diffing.Patches.Properties.Sequential

module Diffing.Patches.Properties.Algebra
  {n : ℕ}{t : T n}{ty : U n}{Δ : Cost} where
\end{code}

\begin{code}
  Ob : Set
  Ob = ElU ty t

  Arr : Ob → Ob → Set
  Arr a b = Σ (Patch t ty) (λ p → D-src p ≡ just a × D-dst p ≡ just b)

  infix 20 _==_

  _==_ : ∀{A B} → Arr A B → Arr A B → Set
  (p , wp) == (q , wq) = p ≡-D q
\end{code}

\begin{code}
  ID : ∀{A} → Arr A A
  ID {A} = (gdiff-id A)
         , gdiff-id-src-lemma A
         , gdiff-id-dst-lemma A

  _⁻¹ : ∀{A B} → Arr A B → Arr B A
  (p , wfp) ⁻¹ = (D-inv p)
               , ((trans (D-inv-src-lemma p) (p2 wfp))
               ,  (trans (D-inv-dst-lemma p) (p1 wfp)))

  infixl 30 _∙_
  
  _∙_ : ∀{A B C} → Arr B C → Arr A B → Arr A C
  _∙_ {A} {B} {C} (p , wp) (q , wq)
    = let p⟶q = ⟶-intro ((((A , B) , p1 wq , p2 wq)
                        , ((B , C) , p1 wp , p2 wp))
                        , trans (p2 wq) (sym (p1 wp)))
      in (comp Δ q p p⟶q)
       , trans (comp-src-lemma Δ q p p⟶q) (p1 wq)
       , trans (comp-dst-lemma Δ q p p⟶q) (p2 wp)
\end{code}

\begin{code}
  ∙-assoc : ∀{A B C D}{p : Arr C D}{q : Arr B C}{r : Arr A B}
          → (p ∙ q) ∙ r == p ∙ (q ∙ r)
  ∙-assoc {A} {B} {C} {D} {p , wp} {q , wq} {r , wr}
    = let wfp   = ((C , D) , p1 wp , p2 wp)
          wfq   = ((B , C) , p1 wq , p2 wq)
          wfr   = ((A , B) , p1 wr , p2 wr)
          q⟶p   = ⟶-intro ((wfq , wfp) , trans (p2 wq) (sym (p1 wp)))
          r⟶q   = ⟶-intro ((wfr , wfq) , trans (p2 wr) (sym (p1 wq)))

          wfqp  = ((B , D) , trans (comp-src-lemma Δ q p q⟶p) (p1 wq)
                           , trans (comp-dst-lemma Δ q p q⟶p) (p2 wp))
          r⟶qp  = ⟶-intro ((wfr , wfqp) , trans (p2 wr) (sym
                                         (trans (comp-src-lemma Δ q p q⟶p)
                                                (p1 wq))))
          wfrq  = ((A , C) , trans (comp-src-lemma Δ r q r⟶q) (p1 wr)
                           , trans (comp-dst-lemma Δ r q r⟶q) (p2 wq))
          rq⟶p  = ⟶-intro ((wfrq , wfp) , trans {!comp-dst-lemma Δ r q r⟶q!}
                                          (trans (p2 wq) (sym (p1 wp))))
       in (trans (comp-src-lemma Δ r (comp Δ q p q⟶p) r⟶qp)
                 (sym (trans (comp-src-lemma Δ (comp Δ r q r⟶q) p rq⟶p)
                             (comp-src-lemma Δ r q r⟶q))))
        , {!!}

  ∙-id-l : ∀{A B}{p : Arr A B} → p ∙ ID == p
  ∙-id-l {A} {B} {p , wp}
    = let idA⟶p = ⟶-intro ((gdiff-id-wf A , (A , B) , p1 wp , p2 wp)
                          , trans (gdiff-id-dst-lemma A) (sym (p1 wp)))
      in (trans (comp-src-lemma Δ (gdiff-id A) p idA⟶p)
         (trans (gdiff-id-src-lemma A) (sym (p1 wp))))
                , comp-dst-lemma Δ (gdiff-id A) p idA⟶p
\end{code}
