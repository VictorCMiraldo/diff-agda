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
    comp (D-inl p) (D-inl q) hip
      = D-inl (comp p q (⟶-inl p q hip))
    comp (D-inl p) (D-setl x x₁) hip
      = D-setl (D-src-wf (p , (D-inl-wf p (p1 (p1 (⟶-elim hip)))))) x₁
    comp (D-inr p) (D-inr q) hip
      = D-inr (comp p q (⟶-inr p q hip))
    comp (D-inr p) (D-setr x x₁) hip
      = {!!}
    comp (D-setl x x₁) (D-inr q) hip
      = {!!}
    comp (D-setl x x₁) (D-setr x₂ x₃) hip
      = {!!}
    comp (D-setr x x₁) (D-inl q) hip
      = {!!}
    comp (D-setr x x₁) (D-setl x₂ x₃) hip
      = {!!}
    
    comp (D-inl p) (D-inr q) hip
      = ⊥-elim (⟶-inl-inr-⊥ p q hip)
    comp (D-inl p) (D-setr x x₁) hip
      = ⊥-elim (⟶-inl-setr-⊥ p x x₁ hip)
    comp (D-inr p) (D-inl q) hip
      = ⊥-elim (⟶-inr-inl-⊥ p q hip)
    comp (D-inr p) (D-setl x x₁) hip
      = ⊥-elim (⟶-inr-setl-⊥ p x x₁ hip)
    comp (D-setl x x₁) (D-inl q) hip
      = ⊥-elim (⟶-setl-inl-⊥ q x x₁ hip)
    comp (D-setl x x₁) (D-setl x₂ x₃) hip
      = ⊥-elim (⟶-setl-setl-⊥ x x₂ x₁ x₃ hip)
    comp (D-setr x x₁) (D-inr q) hip
      = ⊥-elim (⟶-setr-inr-⊥ q x x₁ hip)
    comp (D-setr x x₁) (D-setr x₂ x₃) hip
      = ⊥-elim (⟶-setr-setr-⊥ x x₂ x₁ x₃ hip)
      
    comp (D-pair p p₁) (D-pair q q₁) hip
      = let pq , pq1 = ⟶-pair p q p₁ q₁ hip
         in D-pair (comp p q pq) (comp p₁ q₁ pq1)
    
    comp (D-def p) (D-def q) hip
      = D-def (comp p q (⟶-def p q hip))
    comp (D-top p) (D-top q) hip
      = D-top (comp p q (⟶-top p q hip))
    comp (D-pop p) (D-pop q) hip
      = D-pop (comp p q (⟶-pop p q hip))

    comp (D-mu x) q hip = {!!}

    compμ [] [] hip = []
    compμ [] (x ∷ q) hip = {!!}
    compμ (x ∷ p) [] hip = {!!}
    compμ (x ∷ p) (x₁ ∷ q) hip = {!!}
\end{code}
