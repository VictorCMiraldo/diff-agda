\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Patches.D
open import Diffing.Patches.Properties.WellFounded
open import Diffing.Patches.Properties.Sequential

module Diffing.Patches.Composition where
\end{code}

\begin{code}
  mutual
\end{code}
\begin{code}
    comp : {n : ℕ}{t : T n}{ty : U n}
         → (p q : Patch t ty)(hip : p ⟶ q)
         → Patch t ty

    compμ : {n : ℕ}{t : T n}{ty : U (suc n)}
          → (p q : Patchμ t ty)(hip : p ⟶μ q)
          → Patchμ t ty
         
    comp (D-A ()) q hip
    comp p (D-A ()) hip
    comp D-unit D-unit hip = D-unit
    comp (D-inl p) (D-inl q) hip = D-inl (comp p q (⟶-inl p q hip))
    comp (D-inl p) (D-setl x x₁) hip
      = D-setl (D-src-wf (p , (D-inl-wf p (p1 (p1 (⟶-elim hip)))))) x₁
    comp (D-inl p) (D-inr q) hip
      = ⊥-elim (⟶-inl-inr-⊥ p q hip)
    comp (D-inl p) (D-setr x x₁) hip
      = ⊥-elim (⟶-inl-setr-⊥ p x x₁ hip)
    comp (D-inr p) q hip = {!!}
    comp (D-setl x x₁) q hip = {!!}
    comp (D-setr x x₁) q hip = {!!}
    comp (D-pair p p₁) q hip = {!!}
    comp (D-mu x) q hip = {!!}
    comp (D-def p) q hip = {!!}
    comp (D-top p) q hip = {!!}
    comp (D-pop p) q hip = {!!}

    compμ p q hip = {!!}
\end{code}
