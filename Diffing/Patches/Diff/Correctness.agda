open import Prelude
open import Prelude.ListProperties
  using (lhead-elim; map-lemma; lsplit-elim)
open import Diffing.Universe
open import CF.Properties.Base
  using (plug-correct; plug-spec-fgt; plug-spec-ch)
open import CF.Properties.Mu
  using (μ-close-correct; μ-ar-close-lemma; μ-open-ar-lemma)
open import Diffing.Patches.Diff

open import Relation.Binary.PropositionalEquality

module Diffing.Patches.Diff.Correctness where
  
  open import Prelude.Monad
  open Monad {{...}}

  mutual
    gdiff-src-lemma
      : {n : ℕ}{t : T n}{ty : U n}
      → (x y : ElU ty t)
      → D-src (gdiff x y) ≡ just x

    {-# TERMINATING #-}
    gdiffL-src-lemma
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (xs ys : List (ElU (μ ty) t))
      → Dμ-src (gdiffL xs ys) ≡ just xs

    gdiff-src-lemma unit unit = refl
    gdiff-src-lemma (inl x) (inl y)
      rewrite gdiff-src-lemma x y = refl
    gdiff-src-lemma (inl x) (inr y) = refl
    gdiff-src-lemma (inr x) (inl y) = refl
    gdiff-src-lemma (inr x) (inr y)
      rewrite gdiff-src-lemma x y = refl 
    gdiff-src-lemma (x , x₁) (y , y₁)
      rewrite gdiff-src-lemma x y
            | gdiff-src-lemma x₁ y₁
            = refl
    gdiff-src-lemma (top x) (top y)
      rewrite gdiff-src-lemma x y = refl
    gdiff-src-lemma (pop x) (pop y)
      rewrite gdiff-src-lemma x y = refl
    gdiff-src-lemma (mu x) (mu y)
      rewrite gdiffL-src-lemma (mu x ∷ []) (mu y ∷ [])
            = refl
    gdiff-src-lemma (red x) (red y)
      rewrite gdiff-src-lemma x y = refl

    gdiffL-src-lemma [] [] = refl
    gdiffL-src-lemma [] (y ∷ ys)
      rewrite gdiffL-src-lemma [] (μ-ch y ++ ys) = refl
    gdiffL-src-lemma (x ∷ xs) []
      rewrite gdiffL-src-lemma (μ-ch x ++ xs) []
            | μ-close-correct {a = x} {l = xs} refl
            = refl
    gdiffL-src-lemma (x ∷ xs) (y ∷ ys)
      = ⊔μ-elim-3 {P = λ k → Dμ-src k ≡ just (x ∷ xs)}
          (Dμ-ins (μ-hd y) ∷ gdiffL (x ∷ xs) (μ-ch y ++ ys))
          (Dμ-del (μ-hd x) ∷ gdiffL (μ-ch x ++ xs) (y ∷ ys))
          (Dμ-dwn (gdiff (μ-hd x) (μ-hd y)) ∷ gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys))
          (gdiffL-src-lemma (x ∷ xs) (μ-ch y ++ ys))
          (trans (cong (λ P → P >>= μ-close (μ-hd x) >>= return ∘ cons)
                       (gdiffL-src-lemma (μ-ch x ++ xs) (y ∷ ys)))
                 (cong (λ P → P >>= return ∘ cons) (μ-close-correct {a = x} {l = xs} refl)))
          (trans (cong (λ P → P >>= (λ hdX → Dμ-src (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys))
                                >>= μ-close hdX >>= (return ∘ cons)))
                       (gdiff-src-lemma (μ-hd x) (μ-hd y)))
          (trans (cong (λ P → P >>= μ-close (μ-hd x) >>= (return ∘ cons))
                       (gdiffL-src-lemma (μ-ch x ++ xs) (μ-ch y ++ ys)))
                 (cong (λ P → P >>= return ∘ cons) (μ-close-correct {a = x} {l = xs} refl))))


  mutual
    gdiff-dst-lemma
      : {n : ℕ}{t : T n}{ty : U n}
      → (x y : ElU ty t)
      → D-dst (gdiff x y) ≡ just y

    {-# TERMINATING #-}
    gdiffL-dst-lemma
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (xs ys : List (ElU (μ ty) t))
      → Dμ-dst (gdiffL xs ys) ≡ just ys

    gdiff-dst-lemma unit unit = refl
    gdiff-dst-lemma (inl x) (inl y)
      rewrite gdiff-dst-lemma x y = refl
    gdiff-dst-lemma (inl x) (inr y) = refl
    gdiff-dst-lemma (inr x) (inl y) = refl
    gdiff-dst-lemma (inr x) (inr y)
      rewrite gdiff-dst-lemma x y = refl 
    gdiff-dst-lemma (x , x₁) (y , y₁)
      rewrite gdiff-dst-lemma x y
            | gdiff-dst-lemma x₁ y₁
            = refl
    gdiff-dst-lemma (top x) (top y)
      rewrite gdiff-dst-lemma x y = refl
    gdiff-dst-lemma (pop x) (pop y)
      rewrite gdiff-dst-lemma x y = refl
    gdiff-dst-lemma (mu x) (mu y)
      rewrite gdiffL-dst-lemma (mu x ∷ []) (mu y ∷ [])
            = refl
    gdiff-dst-lemma (red x) (red y)
      rewrite gdiff-dst-lemma x y = refl

    gdiffL-dst-lemma [] [] = refl
    gdiffL-dst-lemma [] (y ∷ ys)
      rewrite gdiffL-dst-lemma [] (μ-ch y ++ ys)
            | μ-close-correct {a = y} {l = ys} refl
            = refl
    gdiffL-dst-lemma (x ∷ xs) []
      rewrite gdiffL-dst-lemma (μ-ch x ++ xs) []
            = refl
    gdiffL-dst-lemma (x ∷ xs) (y ∷ ys)
      = ⊔μ-elim-3 {P = λ k → Dμ-dst k ≡ just (y ∷ ys)}
          (Dμ-ins (μ-hd y) ∷ gdiffL (x ∷ xs) (μ-ch y ++ ys))
          (Dμ-del (μ-hd x) ∷ gdiffL (μ-ch x ++ xs) (y ∷ ys))
          (Dμ-dwn (gdiff (μ-hd x) (μ-hd y)) ∷ gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys))
          (trans (cong (λ P → P >>= μ-close (μ-hd y) >>= return ∘ cons)
                       (gdiffL-dst-lemma (x ∷ xs) (μ-ch y ++ ys)))
                 (cong (λ P → P >>= return ∘ cons) (μ-close-correct {a = y} {l = ys} refl)))
          (gdiffL-dst-lemma (μ-ch x ++ xs) (y ∷ ys))
          (trans (cong (λ P → P >>= (λ hdX → Dμ-dst (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys))
                                >>= μ-close hdX >>= (return ∘ cons)))
                       (gdiff-dst-lemma (μ-hd x) (μ-hd y)))
          (trans (cong (λ P → P >>= μ-close (μ-hd y) >>= (return ∘ cons))
                       (gdiffL-dst-lemma (μ-ch x ++ xs) (μ-ch y ++ ys)))
                 (cong (λ P → P >>= return ∘ cons) (μ-close-correct {a = y} {l = ys} refl))))


  mutual
    gapplyL-Δ-lemma
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → {xs ys : List (ElU (μ ty) t)}(p : List (Dμ ⊥ₚ t ty))
      → Dμ-Δ p ≡ just (xs , ys)
      → gapplyL p xs ≡ just ys

    gapply-Δ-lemma
      : {n : ℕ}{t : T n}{ty : U n}
      → {x y : ElU ty t}(p : Patch t ty)
      → D-Δ p ≡ just (x , y)
      → gapply p x ≡ just y
    gapply-Δ-lemma (D-A x₁) ()
    gapply-Δ-lemma D-unit refl = refl
    gapply-Δ-lemma (D-inl p) hip
      with <M>-elim hip
    gapply-Δ-lemma {x = .(inl h01)} {.(inl h02)} (D-inl p) hip 
      | (h01 , h02) , refl , h2
      = <M>-intro (gapply-Δ-lemma p h2)
    gapply-Δ-lemma (D-inr p) hip
      with <M>-elim hip
    gapply-Δ-lemma {x = .(inr h01)} {.(inr h02)} (D-inr p) hip 
      | (h01 , h02) , refl , h2
      = <M>-intro (gapply-Δ-lemma p h2)
    gapply-Δ-lemma (D-setl xa xb) refl
      rewrite ≟-U-refl xa = refl
    gapply-Δ-lemma (D-setr xa xb) refl
      rewrite ≟-U-refl xa = refl
    gapply-Δ-lemma (D-def p) hip
      with <M>-elim hip
    ...| r , refl , t = <M>-intro (gapply-Δ-lemma p t)
    gapply-Δ-lemma (D-top p) hip
      with <M>-elim hip
    ...| r , refl , t = <M>-intro (gapply-Δ-lemma p t)
    gapply-Δ-lemma (D-pop p) hip
      with <M>-elim hip
    ...| r , refl , t = <M>-intro (gapply-Δ-lemma p t)
    gapply-Δ-lemma (D-pair p p₁) hip
      with <M*>-elim-full {x = D-Δ p₁} hip
    ...| (f , (a0 , a1)) , (b0 , refl , b2) with <M>-elim b0
    ...| (r0 , r1) , s , t
      rewrite s
        | gapply-Δ-lemma p t
        | gapply-Δ-lemma p₁ b2
        = refl
    gapply-Δ-lemma (D-mu x) hip
      with Dμ-Δ x | inspect Dμ-Δ x
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just (sx , dx) | [ X ]
      with <M*>-elim-full {x = lhead dx} hip
    ...| (f , a) , (s0 , s1 , s2)
      with <M>-elim s0
    ...| r0 , r1 , r2
      rewrite r1 | p1 (×-inj s1) | p2 (×-inj s1)
        | lhead-elim sx r2
        | lhead-elim dx s2
        | gapplyL-Δ-lemma x X
        = refl
      
    gapplyL-Δ-lemma [] refl = refl
    gapplyL-Δ-lemma (Dμ-A () ∷ p) hip
    gapplyL-Δ-lemma (Dμ-ins x ∷ p) hip
      with Dμ-Δ p | inspect Dμ-Δ p
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just (sp , dp) | [ SP ] with <M>-elim hip
    ...| r , refl , t rewrite gapplyL-Δ-lemma p SP
      with ar 0 x ≤?-ℕ length dp
    ...| no  _   = ⊥-elim (Maybe-⊥ (sym hip))
    ...| yes prf with lsplit (ar 0 x) dp
    ...| dp0 , dp1 with plug 0 x (map pop dp0)
    ...| nothing = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just x' = t
    gapplyL-Δ-lemma (Dμ-del x ∷ p) hip
      with Dμ-Δ p | inspect Dμ-Δ p
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just (sp , dp) | [ SP ] with <M>-elim hip
    ...| r , refl , t with ar 0 x ≤?-ℕ length sp
    ...| no  _   = ⊥-elim (Maybe-⊥ (sym hip))
    ...| yes prf with lsplit (ar 0 x) sp | inspect (lsplit (ar 0 x)) sp
    ...| sp0 , sp1 | [ SP-split ]
      with plug 0 x (map pop sp0) | inspect (plug 0 x) (map pop sp0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just x' | [ X ]
      rewrite sym (just-inj t)
      with x == fgt 0 x'
    ...| no  abs = ⊥-elim (abs (sym (plug-spec-fgt 0 x' x (map pop sp0) X)))
    ...| yes _ rewrite plug-spec-ch 0 x' x (map pop sp0) X
       = trans (cong (λ P → gapplyL p (P ++ sp1)) (map-lemma sp0 (λ _ → refl)))
        (trans (cong (gapplyL p) (sym (lsplit-elim (ar 0 x) sp SP-split)))
               (gapplyL-Δ-lemma p SP))
    gapplyL-Δ-lemma {ty = ty} (Dμ-dwn x ∷ p) hip
      with D-Δ x | inspect D-Δ x | Dμ-Δ p | inspect Dμ-Δ p
    ...| nothing | _ | _ | _ = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just _  | _ | nothing | _ = ⊥-elim (Maybe-⊥ (sym hip)) 
    ...| just (sx , dx) | [ DX ] | just (sp , dp) | [ DXS ]
      with <M*>-elim-full {x = μ-close dx dp >>= (return ∘ cons)} hip
    ...| (f , a) , (s0 , s1 , s2) with <M>-elim s0
    ...| r0 , r1 , r2 
      with ar 0 sx ≤?-ℕ length sp
    ...| no  _    = ⊥-elim (Maybe-⊥ (sym r2))
    ...| yes arp1
      with ar 0 dx ≤?-ℕ length dp
    ...| no  _    = ⊥-elim (Maybe-⊥ (sym s2))
    ...| yes arp2
      with lsplit (ar 0 sx) sp | inspect (lsplit (ar 0 sx)) sp
    ...| sp0 , sp1 | [ SP ]
      with lsplit (ar 0 dx) dp | inspect (lsplit (ar 0 dx)) dp
    ...| dp0 , dp1 | [ DP ]
      rewrite r1 | p1 (×-inj s1) | p2 (×-inj s1)
      with plug 0 dx (map pop dp0) | inspect (plug 0 dx) (map pop dp0)
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym s2))
    ...| just dx' | [ PDX ]
      with plug 0 sx (map pop sp0) | inspect (plug 0 sx) (map pop sp0)
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym r2))
    ...| just sx' | [ PSX ]
      rewrite p1 (×-inj (just-inj (sym hip)))
            | p2 (×-inj (just-inj (sym hip)))
            | plug-spec-fgt 0 sx' sx (map pop sp0) PSX
            | gapply-Δ-lemma x DX
            | plug-spec-ch 0 sx' sx (map pop sp0) PSX
            | map-lemma {f = pop {a = μ ty}} {g = unpop} sp0 (λ _ → refl)
            | sym (lsplit-elim (ar 0 sx) sp SP)
            | gapplyL-Δ-lemma p DXS
       with ar 0 dx ≤?-ℕ length dp
    ...| no  abs = ⊥-elim (abs arp2)
    ...| yes _ rewrite DP | PDX
       = refl


  gdiff-correct
    : {n : ℕ}{t : T n}{ty : U n}
    → (x y : ElU ty t)
    → gapply (gdiff x y) x ≡ just y
  gdiff-correct x y
    = gapply-Δ-lemma (gdiff x y)
      (src-dst-Δ-lemma x y (gdiff x y) (gdiff-src-lemma x y) (gdiff-dst-lemma x y))
