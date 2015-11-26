\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff
open import Diffing.Patches.Diff.Functor
open import Diffing.Patches.Overlap
open import Diffing.Patches.Residual
open import Diffing.Patches.Conflicts
open import Diffing.Utils.Propositions using (All-++)

open import Data.List.All
open import Relation.Binary.PropositionalEquality
open import Level renaming (zero to lz; suc to ls)

module Diffing.Patches.Merging.Grow where
\end{code}

  Now, one interesting lemma is that
  upon merging two disjoint patches, we
  won't see any update conflict.

%<*merge-sufficient-1-type>
\begin{code}
  merge-sufficient-1 : {n : ℕ}{t : Tel n}{ty : U n}
                    → (d1 d2 : Patch t ty)
                    → NoOverlap d1 d2
                    → All (on-C₀-Set IsGrow) (conflicts (d1 / d2))
\end{code}
%</merge-sufficient-1-type>
\begin{code}
  merge-sufficient-1 (D-A ()) _ _
  merge-sufficient-1 _ (D-A ()) _

  merge-sufficient-1 D-id p prf = []
  merge-sufficient-1 p D-id prf
    rewrite /-id p | forget-cast {A = C} p
      = []

  merge-sufficient-1 D-void D-void prf = []

  merge-sufficient-1 (D-inl d1) (D-inl d2) prf
    with d1 / d2 | inspect (_/_ d1) d2
  ...| nothing | _ = []
  ...| just d12 | [ R ] rewrite sym R
     = subst (All (on-C₀-Set IsGrow))
             (subst (λ P → conflicts P ≡ forget d12) (sym R) refl)
             (merge-sufficient-1 d1 d2 prf)
  merge-sufficient-1 (D-inl d1) (D-inr d2) prf = []
  merge-sufficient-1 (D-inl d1) (D-setl x x₁) prf
    rewrite prf x | ≟-U-refl x = []
  merge-sufficient-1 (D-inl d1) (D-setr x x₁) prf = []
  merge-sufficient-1 (D-inr d1) (D-inl d2) prf = []
  merge-sufficient-1 (D-inr d1) (D-inr d2) prf
    with d1 / d2 | inspect (_/_ d1) d2
  ...| nothing | _ = []
  ...| just d12 | [ R ] rewrite sym R
     = subst (All (on-C₀-Set IsGrow))
             (subst (λ P → conflicts P ≡ forget d12) (sym R) refl)
             (merge-sufficient-1 d1 d2 prf)
  merge-sufficient-1 (D-inr d1) (D-setl x x₁) prf = []
  merge-sufficient-1 (D-inr d1) (D-setr x x₁) prf
    rewrite prf x | ≟-U-refl x = []
  merge-sufficient-1 (D-setl x x₁) (D-inl d2) prf
    rewrite prf x | ≟-U-refl x = []
  merge-sufficient-1 (D-setl x x₁) (D-inr d2) prf = []
  merge-sufficient-1 (D-setl x x₁) (D-setl x₂ x3) prf with x ≟-U x₂
  ...| no  _ = []
  merge-sufficient-1 (D-setl x x₁) (D-setl x₂ .x₁) refl
     | yes p rewrite ≟-U-refl x₁ = []
  merge-sufficient-1 (D-setl x x₁) (D-setr x₂ x₃) prf = []
  merge-sufficient-1 (D-setr x x₁) (D-inl d2) prf = []
  merge-sufficient-1 (D-setr x x₁) (D-inr d2) prf
    rewrite prf x | ≟-U-refl x = []
  merge-sufficient-1 (D-setr x x₁) (D-setl x₂ x₃) prf = []
  merge-sufficient-1 (D-setr x x₁) (D-setr x₂ x₃) prf with x ≟-U x₂
  ...| no _ = []
  merge-sufficient-1 (D-setr x x₁) (D-setr x₂ .x₁) refl
     | yes p rewrite ≟-U-refl x₁ = []
  merge-sufficient-1 {t = t} {ty = a ⊗ b} (D-pair d1 d2) (D-pair d3 d4) prf
    with d2 / d4 | inspect (_/_ d2) d4
  ...| nothing | _ = []
  ...| just d24 | [ R24 ] with d1 / d3 | inspect (_/_ d1) d3
  ...| nothing | _ = []
  ...| just d13 | [ R13 ]
     with merge-sufficient-1 d1 d3 (p1 prf)
        | merge-sufficient-1 d2 d4 (p2 prf)
  ...| h1 | h2 rewrite R13 | R24 =  All-++ h1 h2
  merge-sufficient-1 (D-β d1) (D-β d2) prf
    with d1 / d2 | inspect (_/_ d1) d2
  ...| nothing | _ = []
  ...| just d12 | [ R ] rewrite sym R
     = subst (All (on-C₀-Set IsGrow))
             (subst (λ P → conflicts P ≡ forget d12) (sym R) refl)
             (merge-sufficient-1 d1 d2 prf)
  merge-sufficient-1 (D-top d1) (D-top d2) prf
    with d1 / d2 | inspect (_/_ d1) d2
  ...| nothing | _ = []
  ...| just d12 | [ R ] rewrite sym R
     = subst (All (on-C₀-Set IsGrow))
             (subst (λ P → conflicts P ≡ forget d12) (sym R) refl)
             (merge-sufficient-1 d1 d2 prf)
  merge-sufficient-1 (D-pop d1) (D-pop d2) prf
    with d1 / d2 | inspect (_/_ d1) d2
  ...| nothing | _ = []
  ...| just d12 | [ R ] rewrite sym R
     = subst (All (on-C₀-Set IsGrow))
             (subst (λ P → conflicts P ≡ forget d12) (sym R) refl)
             (merge-sufficient-1 d1 d2 prf)
  merge-sufficient-1 (D-mu d1) (D-mu d2) prf
    with res d1 d2 | inspect (res d1) d2
  ...| nothing | _ = []
  ...| just r12 | [ R12 ]
    = subst (All (on-C₀-Set IsGrow))
             (subst (λ P → conflictsμ P ≡ forgetμ r12) (sym R12) refl)
             (aux d1 d2 prf)
    where
      wrap : {n : ℕ}{t : Tel n}{ty : U (suc n)}
           → (d1 d2 : Patchμ t ty){k : List (Dμ C t ty)}
           → res d1 d2 ≡ just k
           → All (on-C₀-Set IsGrow) (conflictsμ (res d1 d2))
           → All (on-C₀-Set IsGrow) (forgetμ k)
      wrap d1 d2 R a rewrite R = a

      aux : {n : ℕ}{t : Tel n}{ty : U (suc n)}
          → (d1 d2 : Patchμ t ty)
          → NoOverlapμ d1 d2
          → All (on-C₀-Set IsGrow) (conflictsμ (res d1 d2))
      aux [] [] prf₁ = []
      aux _ (Dμ-A () ∷ _) _
      aux (Dμ-A () ∷ _) _ _

      aux [] (Dμ-ins x ∷ d2) prf
        with res [] d2 | inspect (res []) d2
      ...| nothing | _ = []
      ...| just r | [ R ]
        = unit ∷ (subst (All (on-C₀-Set IsGrow))
          (subst (λ P → conflictsμ P ≡ forgetμ r) (sym R) refl)
          (aux [] d2 unit))

      aux (Dμ-ins x ∷ d1) [] prf
        with res d1 [] | inspect (res d1) []
      ...| nothing | _ = []
      ...| just r | [ R ]
        = unit ∷ wrap d1 [] R (aux d1 [] (subst id (sym (NoOverlapμ-[] d1)) unit))

      aux (Dμ-ins x ∷ d1) (Dμ-ins y ∷ d2) prf with x ≟-U y
      aux (Dμ-ins x ∷ d1) (Dμ-ins y ∷ d2) prf | no ¬p
        with res d1 d2 | inspect (res d1) d2
      ...| nothing | _ = []
      ...| just d12 | [ R ]
        = unit ∷ wrap d1 d2 R (aux d1 d2 prf)
      aux (Dμ-ins x ∷ d1) (Dμ-ins y ∷ d2) prf | yes p
        with res d1 d2 | inspect (res d1) d2
      ...| nothing | _ = []
      ...| just d12 | [ R ] = wrap d1 d2 R (aux d1 d2 prf)

      aux (Dμ-del x ∷ d1) (Dμ-ins y ∷ d2) prf
        with res (Dμ-del x ∷ d1) d2 | inspect (res (Dμ-del x ∷ d1)) d2
      ...| nothing | _ = []
      ...| just r | [ R ]
        = unit ∷ wrap (Dμ-del x ∷ d1) d2 R (aux (Dμ-del x ∷ d1) d2 prf)
      aux (Dμ-cpy x ∷ d1) (Dμ-ins y ∷ d2) prf
        with res (Dμ-cpy x ∷ d1) d2 | inspect (res (Dμ-cpy x ∷ d1)) d2
      ...| nothing | _ = []
      ...| just r | [ R ]
        = unit ∷ wrap (Dμ-cpy x ∷ d1) d2 R (aux (Dμ-cpy x ∷ d1) d2 prf)
      aux (Dμ-dwn x dx ∷ d1) (Dμ-ins y ∷ d2) prf
        with res (Dμ-dwn x dx ∷ d1) d2 | inspect (res (Dμ-dwn x dx ∷ d1)) d2
      ...| nothing | _ = []
      ...| just r | [ R ]
        = unit ∷ wrap (Dμ-dwn x dx ∷ d1) d2 R (aux (Dμ-dwn x dx ∷ d1) d2 prf)

      aux [] (Dμ-del x ∷ d3) _ = []
      aux [] (Dμ-cpy x ∷ d3) _ = []
      aux [] (Dμ-dwn x x₁ ∷ d3) _ = []
      aux (Dμ-del x ∷ d3) [] prf₁ = []
      aux (Dμ-cpy x ∷ d3) [] prf₁ = []
      aux (Dμ-dwn x x₁ ∷ d3) [] prf₁ = []

      aux (Dμ-ins x ∷ d1) (Dμ-del y ∷ d2) prf
        with res d1 (Dμ-del y ∷ d2) | inspect (res d1) (Dμ-del y ∷ d2)
      ...| nothing | _ = []
      ...| just r | [ R ]
        = unit ∷ wrap d1 (Dμ-del y ∷ d2) R (aux d1 (Dμ-del y ∷ d2) prf)
      aux (Dμ-ins x ∷ d1) (Dμ-cpy y ∷ d2) prf
        with res d1 (Dμ-cpy y ∷ d2) | inspect (res d1) (Dμ-cpy y ∷ d2)
      ...| nothing | _ = []
      ...| just r | [ R ]
        = unit ∷ wrap d1 (Dμ-cpy y ∷ d2) R (aux d1 (Dμ-cpy y ∷ d2) prf)
      aux (Dμ-ins x ∷ d1) (Dμ-dwn y dy ∷ d2) prf
        with res d1 (Dμ-dwn y dy ∷ d2) | inspect (res d1) (Dμ-dwn y dy ∷ d2)
      ...| nothing | _ = []
      ...| just r | [ R ]
        = unit ∷ wrap d1 (Dμ-dwn y dy ∷ d2) R (aux d1 (Dμ-dwn y dy ∷ d2) prf)

      aux (Dμ-del x ∷ d1) (Dμ-del y ∷ d2) prf with x ≟-U y
      ...| no p = []
      ...| yes p = aux d1 d2 prf
      aux (Dμ-del x ∷ d1) (Dμ-cpy y ∷ d2) prf with x ≟-U y
      ...| no p = []
      ...| yes p with res d1 d2 | inspect (res d1) d2
      ...| nothing | _ = []
      ...| just d12 | [ R ] = wrap d1 d2 R (aux d1 d2 prf)
      aux (Dμ-del x ∷ d1) (Dμ-dwn y dy ∷ d2) prf with x ≟-U y
      ...| yes p with y ≟-U x
      aux (Dμ-del x ∷ d3) (Dμ-dwn y dy ∷ d4) () | yes p | yes q
      aux (Dμ-del x ∷ d1) (Dμ-dwn y dy ∷ d2) prf | yes p | no q
        = []
      aux (Dμ-del x ∷ d1) (Dμ-dwn y dy ∷ d2) prf | no p with y ≟-U x
      aux (Dμ-del x ∷ d3) (Dμ-dwn y dy ∷ d4) prf₁ | no p₁ | yes p
        = ⊥-elim (p₁ (sym p))
      aux (Dμ-del x ∷ d3) (Dμ-dwn y dy ∷ d4) prf₁ | no p | no ¬p
        = []
      aux (Dμ-cpy x ∷ d1) (Dμ-del y ∷ d2) prf with x ≟-U y
      ...| no p = []
      ...| yes p with res d1 d2 | inspect (res d1) d2
      ...| nothing | _ = []
      ...| just d12 | [ R ] = wrap d1 d2 R (aux d1 d2 prf)
      aux (Dμ-cpy x ∷ d1) (Dμ-cpy y ∷ d2) prf with x ≟-U y
      ...| no p = []
      ...| yes p with res d1 d2 | inspect (res d1) d2
      ...| nothing | _ = []
      ...| just d12 | [ R ] = wrap d1 d2 R (aux d1 d2 prf)
      aux (Dμ-cpy x ∷ d1) (Dμ-dwn y dy ∷ d2) prf with x ≟-U y
      ...| no p = []
      ...| yes p with gapply dy (red x)
      ...| nothing = []
      ...| just (red x') with res d1 d2 | inspect (res d1) d2
      ...| nothing | _ = []
      ...| just d12 | [ R ] = wrap d1 d2 R (aux d1 d2 prf)
      aux (Dμ-dwn x dx ∷ d1) (Dμ-del y ∷ d2) prf with x ≟-U y
      ...| no p = []
      aux (Dμ-dwn x dx ∷ d3) (Dμ-del y ∷ d4) () | yes p
      aux (Dμ-dwn x dx ∷ d1) (Dμ-cpy y ∷ d2) prf with x ≟-U y
      ...| no p = []
      ...| yes p with gapply dx (red y)
      ...| nothing = []
      ...| just (red x') with res d1 d2 | inspect (res d1) d2
      ...| nothing | _ = []
      ...| just d12 | [ R ] rewrite forget-cast {A = C} dx
         = wrap d1 d2 R (aux d1 d2 prf)
      aux (Dμ-dwn x dx ∷ d1) (Dμ-dwn y dy ∷ d2) prf with x ≟-U y
      ...| no p = []
      ...| yes p with res d1 d2 | inspect (res d1) d2
      ...| nothing | _ = []
      ...| just d12 | [ R12 ] with dx / dy | inspect (_/_ dx) dy
      ...| nothing | _ = []
      ...| just dxy | [ Rxy ] with merge-sufficient-1 dx dy (p1 prf)
      ...| hip1 rewrite Rxy = All-++ hip1 (wrap d1 d2 R12 (aux d1 d2 (p2 prf)))
\end{code}
