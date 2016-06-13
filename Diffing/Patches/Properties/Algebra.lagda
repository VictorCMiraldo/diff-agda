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
  
  _∙_ : ∀{A B C} → Arr B C → Arr A B → Arr A C
  _∙_ {A} {B} {C} (p , wp) (q , wq)
    = let p⟶q = ⟶-intro ((((A , B) , p1 wq , p2 wq)
                        , ((B , C) , p1 wp , p2 wp))
                        , trans (p2 wq) (sym (p1 wp)))
      in (comp Δ q p p⟶q)
       , trans (comp-src-lemma Δ q p p⟶q) (p1 wq)
       , trans (comp-dst-lemma Δ q p p⟶q) (p2 wp)
\end{code}
