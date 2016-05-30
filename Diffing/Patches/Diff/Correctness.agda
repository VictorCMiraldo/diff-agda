open import Prelude
open import Diffing.Universe
open import CF.Properties.Base
  using (plug-correct)
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
    gapply-src-dst-lemma
      : {n : ℕ}{t : T n}{ty : U n}
      → {x y : ElU ty t}(p : Patch t ty)
      → D-src p ≡ just x
      → D-dst p ≡ just y
      → gapply p x ≡ just y
    gapply-src-dst-lemma (D-A x₁) hx hy = {!!}
    gapply-src-dst-lemma D-unit hx hy = {!!}
    gapply-src-dst-lemma {x = inl x} {inl y} (D-inl p) hx hy = {!!}
    gapply-src-dst-lemma {x = inl x} {inr y} (D-inl p) hx hy = {!!}
    gapply-src-dst-lemma {x = inr x} {inl y} (D-inl p) hx hy = {!!}
    gapply-src-dst-lemma {x = inr x} {inr y} (D-inl p) hx hy = {!!}
    gapply-src-dst-lemma (D-inr p) hx hy = {!!}
    gapply-src-dst-lemma (D-setl x₁ x₂) hx hy = {!!}
    gapply-src-dst-lemma (D-setr x₁ x₂) hx hy = {!!}
    gapply-src-dst-lemma (D-pair p p₁) hx hy = {!!}
    gapply-src-dst-lemma (D-mu x₁) hx hy = {!!}
    gapply-src-dst-lemma (D-def p) hx hy = {!!}
    gapply-src-dst-lemma (D-top p) hx hy = {!!}
    gapply-src-dst-lemma (D-pop p) hx hy = {!!}
      
