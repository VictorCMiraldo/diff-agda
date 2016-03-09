\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Patches.Diff

module Diffing.Patches.Overlap where
\end{code}

  One important characteristic of any merging algorithm
  is the hability to merge disjoint patches without conflicts.
  
  But then, we need a solid notion of what
  it means to be a disjoint patch.

\begin{code}
  mutual
    NoOverlap : {n : ℕ}{t : Tel n}{ty : U n}
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
      = ∀ x → gapply d1 x ≡ just x
    NoOverlap (D-inr d1)   (D-setr x y)
      = ∀ x → gapply d1 x ≡ just x
    NoOverlap (D-setl x y) (D-inl d2)
      = ∀ x → gapply d2 x ≡ just x
    NoOverlap (D-setr x y) (D-inr d2)
      = ∀ x → gapply d2 x ≡ just x
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

    NoOverlap (D-β d1)   (D-β d2)   = NoOverlap d1 d2
    NoOverlap (D-top d1) (D-top d2) = NoOverlap d1 d2
    NoOverlap (D-pop d1) (D-pop d2) = NoOverlap d1 d2
    NoOverlap (D-mu d1)  (D-mu d2)  = NoOverlapμ d1 d2

    -- Fixed points can be complicated.
    NoOverlapμ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
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
    NoOverlapμ (Dμ-del x ∷ xs) (Dμ-dwn y dy ∷ ys) with x ≟-U y
    ...| no  _ = Unit
    ...| yes _ = ⊥
    NoOverlapμ (Dμ-dwn x dx ∷ xs) (Dμ-del y ∷ ys) with x ≟-U y
    ...| no  _ = Unit
    ...| yes _ = ⊥
    -- Here, the units refer to non-aligned patches,
    -- the only really interesting case is the dwn case.
    NoOverlapμ (Dμ-del x ∷ xs) (Dμ-del y ∷ ys) with x ≟-U y
    ...| no  _ = Unit
    ...| yes _ = NoOverlapμ xs ys
    NoOverlapμ (Dμ-del x ∷ xs) (Dμ-cpy y ∷ ys) with x ≟-U y
    ...| no  _ = Unit
    ...| yes _ = NoOverlapμ xs ys    
    NoOverlapμ (Dμ-cpy x ∷ xs) (Dμ-del y ∷ ys) with x ≟-U y
    ...| no  _ = Unit
    ...| yes _ = NoOverlapμ xs ys
    NoOverlapμ (Dμ-cpy x ∷ xs) (Dμ-cpy y ∷ ys) with x ≟-U y
    ...| no  _ = Unit
    ...| yes _ = NoOverlapμ xs ys
    NoOverlapμ (Dμ-cpy x ∷ xs) (Dμ-dwn y dy ∷ ys) with x ≟-U y
    ...| no  _ = Unit
    ...| yes _ = NoOverlapμ xs ys
    NoOverlapμ (Dμ-dwn x dx ∷ xs) (Dμ-cpy y ∷ ys) with x ≟-U y
    ...| no  _ = Unit
    ...| yes _ = NoOverlapμ xs ys
    NoOverlapμ (Dμ-dwn x dx ∷ xs) (Dμ-dwn y dy ∷ ys) with x ≟-U y
    ...| no  _ = Unit
    ...| yes _ = NoOverlap dx dy × NoOverlapμ xs ys
\end{code}

\begin{code}
  NoOverlapμ-[] : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                → (d1 : Patchμ t ty)
                → NoOverlapμ d1 [] ≡ Unit
  NoOverlapμ-[] [] = refl
  NoOverlapμ-[] (Dμ-A () ∷ d1)
  NoOverlapμ-[] (Dμ-ins x ∷ d1) = refl
  NoOverlapμ-[] (Dμ-del x ∷ d1) = refl
  NoOverlapμ-[] (Dμ-cpy x ∷ d1) = refl
  NoOverlapμ-[] (Dμ-dwn x x₁ ∷ d1) = refl
\end{code}
