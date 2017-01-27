\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Patches.D
open import Diffing.Patches.Id
open import Diffing.Patches.Composition
open import Diffing.Patches.Properties.WellFormed
open import Diffing.Patches.Properties.Sequential
open import Diffing.Patches.Cost
open import Diffing.Diff

module Diffing.Patches.Properties.Overlap where
\end{code}

  One important characteristic of any merging algorithm
  is the hability to merge disjoint patches without conflicts.
  
  But then, we need a solid notion of what
  it means to be a disjoint patch.

\begin{code}
  mutual
    NoOverlap : {n : ℕ}{t : T n}{ty : U n}
              → (d1 d2 : Patch t ty)
              → Set
    NoOverlap (D-A ()) _
    NoOverlap _ (D-A ())

    -- Id's don't overlap anything.
    -- NoOverlap D-id _ = Unit
    -- NoOverlap _ D-id = Unit

    -- neither do units.
    NoOverlap D-unit D-unit = Unit

    -- Coproducts are the hardest.
    NoOverlap (D-inl d1)   (D-inl d2) = NoOverlap d1 d2
    NoOverlap (D-inr d1)   (D-inr d2) = NoOverlap d1 d2
    NoOverlap (D-inl d1)   (D-setl x y) 
      = Is-diff-id d1
    NoOverlap (D-inr d1)   (D-setr x y)
      = Is-diff-id d1
    NoOverlap (D-setl x y) (D-inl d2)
      = Is-diff-id d2
    NoOverlap (D-setr x y) (D-inr d2)
      = Is-diff-id d2
    NoOverlap (D-setl x y) (D-setl w z) with x ≟-U w
    ...| no  _ = Unit
    ...| yes _ = y ≡ z
    NoOverlap (D-setr x y) (D-setr w z) with x ≟-U w
    ...| no  _ = Unit
    ...| yes _ = y ≡ z

    -- But then, non-aligned edits are trivially non-overlapping.
    NoOverlap (D-inl d1)   (D-inr d2)   = Unit
    NoOverlap (D-inl d1)   (D-setr x y) = Unit
    NoOverlap (D-inr d1)   (D-inl d2)   = Unit
    NoOverlap (D-inr d1)   (D-setl x y) = Unit
    NoOverlap (D-setl x y) (D-inr d2)   = Unit
    NoOverlap (D-setl x y) (D-setr w z) = Unit
    NoOverlap (D-setr x y) (D-inl d2)   = Unit
    NoOverlap (D-setr x y) (D-setl w z) = Unit

    NoOverlap (D-pair d1 d2) (D-pair d3 d4)
      = NoOverlap d1 d3 × NoOverlap d2 d4

    NoOverlap (D-def d1) (D-def d2)   = NoOverlap d1 d2
    NoOverlap (D-top d1) (D-top d2) = NoOverlap d1 d2
    NoOverlap (D-pop d1) (D-pop d2) = NoOverlap d1 d2
    NoOverlap (D-mu d1)  (D-mu d2)  = NoOverlapμ d1 d2

    -- Fixed points can be complicated.
    NoOverlapμ : {n : ℕ}{t : T n}{ty : U (suc n)}
               → (d1 d2 : Patchμ t ty)
               → Set
    NoOverlapμ (Dμ-A () ∷ d1) (_ ∷ d2)
    NoOverlapμ (_ ∷ d1) (Dμ-A () ∷ d2)

    -- Same argument, non-aligned edits are trivially
    -- non-overlapping.
    NoOverlapμ [] _ = Unit
    NoOverlapμ _ [] = Unit

    -- Insertions are trivialy non-overlapping.
    NoOverlapμ (Dμ-ins _ ∷ xs) (Dμ-ins _ ∷ ys) 
      = NoOverlapμ xs ys
    NoOverlapμ (Dμ-ins _ ∷ xs) ys = NoOverlapμ xs ys
    NoOverlapμ xs (Dμ-ins _ ∷ ys) = NoOverlapμ xs ys

    -- The following two cases are interesting,
    -- If one is deleting an element that has been altered
    -- the patches are overlaping.
    -- However, if the elements differ, they are not aligned,
    -- and, therefore, trivially non-overlapping.
    NoOverlapμ (Dμ-del x ∷ xs) (Dμ-dwn y ∷ ys) 
      = Is-diff-id y × NoOverlapμ xs ys
    NoOverlapμ (Dμ-dwn x ∷ xs) (Dμ-del y ∷ ys) 
      = Is-diff-id x × NoOverlapμ xs ys
    -- Here, the units refer to non-aligned patches,
    -- the only really interesting case is the dwn case.
    NoOverlapμ (Dμ-del x ∷ xs) (Dμ-del y ∷ ys) with x ≟-U y
    ...| no  _ = Unit
    ...| yes _ = NoOverlapμ xs ys
    NoOverlapμ (Dμ-dwn x ∷ xs) (Dμ-dwn y ∷ ys)
      = NoOverlap x y × NoOverlapμ xs ys
\end{code}

\begin{code}
  NoOverlapμ-[] : {n : ℕ}{t : T n}{ty : U (suc n)}
                → (d1 : Patchμ t ty)
                → NoOverlapμ d1 [] ≡ Unit
  NoOverlapμ-[] [] = refl
  NoOverlapμ-[] (Dμ-A () ∷ d1)
  NoOverlapμ-[] (Dμ-ins x ∷ d1) = refl
  NoOverlapμ-[] (Dμ-del x ∷ d1) = refl
  NoOverlapμ-[] (Dμ-dwn x ∷ d1) = refl
\end{code}

\begin{code}
  comp-cost : {n : ℕ}{t : T n}{ty : U n}{Δ : Cost}
            → (p q : Patch t ty)(hip : p ⟶ q)(ovr : NoOverlap p q)
            → cost Δ (comp Δ p q hip) ≡ cost Δ p + cost Δ q
  comp-cost (D-A ()) q hip ovr
  comp-cost p (D-A ()) hip ovr
  comp-cost D-unit D-unit hip ovr = refl
  comp-cost (D-inl p) (D-inl q) hip ovr 
    = comp-cost p q (⟶-inl p q hip) ovr
  comp-cost {Δ = Δ} (D-inl p) (D-setl x x₁) hip ovr
    with ⟶-inl-setl p x x₁ hip
  ...| hip' = {!!}
  comp-cost (D-inl p) (D-inr q) hip ovr
    = ⊥-elim (⟶-inl-inr-⊥ p q hip)
  comp-cost (D-inl p) (D-setr x x₁) hip ovr 
    = ⊥-elim (⟶-inl-setr-⊥ p x x₁ hip)
  comp-cost (D-inr p) q hip ovr = {!!}
  comp-cost (D-setl x x₁) q hip = {!!}
  comp-cost (D-setr x x₁) q hip = {!!}
  comp-cost (D-pair p p₁) (D-pair q q₁) hip ovr = {!!}
  comp-cost (D-mu x) q hip = {!!}
  comp-cost (D-def p) q hip = {!!}
  comp-cost (D-top p) q hip = {!!}
  comp-cost (D-pop p) q hip = {!!}

  compμ-cost : {n : ℕ}{t : T n}{ty : U (suc n)}{Δ : Cost}
            → (p q : Patchμ t ty)(hip : p ⟶μ q)(ovr : NoOverlapμ p q)
            → costL Δ (compμ Δ p q hip) ≡ costL Δ p + costL Δ q
  compμ-cost [] [] hip ovr = refl
  compμ-cost [] (x ∷ q) hip ovr = {!!}
  compμ-cost (x ∷ p) [] hip ovr = {!!}
  compμ-cost (x ∷ p) (x₁ ∷ q) hip ovr = {!!}
\end{code}
