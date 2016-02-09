\begin{code}
open import Prelude
open import Data.Nat using (_≤_)
open import Diffing.Universe.Syntax
open import Diffing.Universe.MuUtils
open import Diffing.Universe.Equality
open import Diffing.Universe.Measures
open import Diffing.Patches.Diff
open import Diffing.Utils.Propositions

module Diffing.Patches.Diff.Inverse where

  open import Diffing.Utils.Monads
  open Monad {{...}}

  open import Data.Nat.Properties.Simple using (+-comm)
\end{code}

\begin{code}
  mutual
\end{code}
%<*D-inv-type>
\begin{code}
    D-inv : {n : ℕ}{t : Tel n}{ty : U n}
          → Patch t ty → Patch t ty
\end{code}
%</D-inv-type>
\begin{code}
    D-inv (D-A ())
    D-inv D-void = D-void
    D-inv (D-inl p) = D-inl (D-inv p)
    D-inv (D-inr p) = D-inr (D-inv p)
    D-inv (D-setl x y) = D-setr y x
    D-inv (D-setr x y) = D-setl y x
    D-inv (D-pair p q) = D-pair (D-inv p) (D-inv q)
    D-inv (D-mu x) = D-mu (Dμ-inv x)
    D-inv (D-β p) = D-β (D-inv p)
    D-inv (D-top p) = D-top (D-inv p)
    D-inv (D-pop p) = D-pop (D-inv p)
    
    {-# TERMINATING #-}
    Dμ-inv : {n : ℕ}{t : Tel n}{ty : U (suc n)}
           → Patchμ t ty → Patchμ t ty
    Dμ-inv = map Dμ-inv1

    Dμ-inv1 : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            → Dμ ⊥ₚ t ty → Dμ ⊥ₚ t ty
    Dμ-inv1 (Dμ-A ())
    Dμ-inv1 (Dμ-ins x) = Dμ-del x
    Dμ-inv1 (Dμ-del x) = Dμ-ins x
    Dμ-inv1 (Dμ-dwn x) = Dμ-dwn (D-inv x)
\end{code}

\begin{code}
  mutual
\end{code}
%<*D-inv-cost-type>
\begin{code}
    D-inv-cost : {n : ℕ}{t : Tel n}{ty : U n}
               → (d : Patch t ty)
               → cost d ≡ cost (D-inv d)
\end{code}
%</D-inv-cost-type>
\begin{code}
    D-inv-cost (D-A ())
    D-inv-cost D-void = refl
    D-inv-cost (D-inl d) = D-inv-cost d
    D-inv-cost (D-inr d) = D-inv-cost d
    D-inv-cost (D-setl x x₁) = cong₂ _+_ (+-comm (sizeElU x) (sizeElU x₁)) 
                               (cong (λ P → P + zero) (+-comm (sizeElU x) (sizeElU x₁)))
    D-inv-cost (D-setr x x₁) = cong₂ _+_ (+-comm (sizeElU x) (sizeElU x₁)) 
                               (cong (λ P → P + zero) (+-comm (sizeElU x) (sizeElU x₁)))
    D-inv-cost (D-pair p q) = cong₂ _+_ (D-inv-cost p) (D-inv-cost q)
    D-inv-cost (D-mu x) = Dμ-inv-costL x
    D-inv-cost (D-β d) = D-inv-cost d
    D-inv-cost (D-top d) = D-inv-cost d
    D-inv-cost (D-pop d) = D-inv-cost d

    Dμ-inv-costL : {n : ℕ}{t : Tel n}{ty : U (suc n)}
               → (d : Patchμ t ty)
               → costL d ≡ costL (Dμ-inv d)
    Dμ-inv-costL [] = refl
    Dμ-inv-costL (Dμ-A () ∷ d)
    Dμ-inv-costL (Dμ-ins x ∷ d) = cong (λ P → 1 + sizeElU x + P) (Dμ-inv-costL d)
    Dμ-inv-costL (Dμ-del x ∷ d) = cong (λ P → 1 + sizeElU x + P) (Dμ-inv-costL d)
    Dμ-inv-costL (Dμ-dwn x ∷ d) = cong₂ _+_ (D-inv-cost x) (Dμ-inv-costL d)

    Dμ-inv-cost : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                → (d : Dμ ⊥ₚ t ty)
                → costμ d ≡ costμ (Dμ-inv1 d)
    Dμ-inv-cost (Dμ-A ())
    Dμ-inv-cost (Dμ-ins x) = refl
    Dμ-inv-cost (Dμ-del x) = refl
    Dμ-inv-cost (Dμ-dwn x) = D-inv-cost x
\end{code}

\begin{code}
  gapply-⊔-inv : {n : ℕ}{t : Tel n}{ty : U (suc n)}{a b : List (ElU (μ ty) t)}
                 {d1 d2 : Patchμ t ty}
               → gapplyL (Dμ-inv d1) a ≡ just b
               → gapplyL (Dμ-inv d2) a ≡ just b
               → gapplyL (Dμ-inv (d1 ⊔μ d2)) a ≡ just b
  gapply-⊔-inv {a = a} {b = b} {d1 = d1} {d2 = d2} pa pb 
    = ⊔μ-elim {P = λ p → gapplyL (Dμ-inv p) a ≡ just b} 
              d1 d2 pa pb

  mutual    
    {-# TERMINATING #-}
\end{code}
%<*D-inv-sound-type>
\begin{code}
    D-inv-sound 
      : {n : ℕ}{t : Tel n}{ty : U n}
      → (a b : ElU ty t)
      → gapply (D-inv (gdiff a b)) b ≡ just a
\end{code}
%</D-inv-sound-type>
\begin{code}
    D-inv-sound void void = refl
    D-inv-sound (inl a) (inl b) 
      rewrite D-inv-sound a b = refl
    D-inv-sound (inl a) (inr b) 
      rewrite ≟-U-refl b = refl
    D-inv-sound (inr a) (inl b) 
      rewrite ≟-U-refl b = refl
    D-inv-sound (inr a) (inr b) 
      rewrite D-inv-sound a b = refl 
    D-inv-sound (a₁ , a₂) (b₁ , b₂) 
      rewrite D-inv-sound a₁ b₁ 
            | D-inv-sound a₂ b₂ = refl
    D-inv-sound (top a) (top b) 
      rewrite D-inv-sound a b = refl 
    D-inv-sound (pop a) (pop b) 
      rewrite D-inv-sound a b = refl 
    D-inv-sound (mu a) (mu b) 
      = cong (λ P → P >>= safeHead)
             (Dμ-inv-sound (mu a ∷ []) (mu b ∷ []))
    D-inv-sound (red a) (red b)
      rewrite D-inv-sound a b = refl

    mu-ins-L : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                     → {as bs : List (ElU (μ ty) t)}
                     → (b : ElU (μ ty) t)
                     → gapplyL (Dμ-inv (Dμ-ins (μ-hd b) ∷ gdiffL as (μ-ch b ++ bs))) (b ∷ bs)
                     ≡ just as
    mu-ins-L {as = as} {bs = bs} b
      rewrite ≟-U-refl (μ-hd b)
            = Dμ-inv-sound as (μ-ch b ++ bs)

    mu-del-L : {n : ℕ}{t : Tel n}{ty : U (suc n)}
             → {as bs : List (ElU (μ ty) t)}
             → (a : ElU (μ ty) t)
             → gapplyL (Dμ-inv (Dμ-del (μ-hd a) ∷ gdiffL (μ-ch a ++ as) bs)) bs
             ≡ just (a ∷ as)
    mu-del-L {as = as} {bs = bs} a
      rewrite Dμ-inv-sound (μ-ch a ++ as) bs 
            | μ-close-resp-arity {hdA = μ-hd a} {chA = μ-ch a} {l = as} refl 
            = refl

    mu-down-L : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                     → {as bs : List (ElU (μ ty) t)}
                     → (a b : ElU (μ ty) t)
                     → gapplyL (Dμ-inv (Dμ-dwn (gdiff (μ-hd a) (μ-hd b)) ∷ 
                                gdiffL (μ-ch a ++ as) (μ-ch b ++ bs))) (b ∷ bs)
                     ≡ just (a ∷ as)
    mu-down-L {as = as} {bs = bs} a b
      rewrite ≟-U-refl (μ-hd b)
            | D-inv-sound (μ-hd a) (μ-hd b)
            | Dμ-inv-sound (μ-ch a ++ as) (μ-ch b ++ bs)
            | μ-close-resp-arity {hdA = μ-hd a} {chA = μ-ch a} {l = as} refl 
            = refl

    Dμ-inv-sound
      : {n : ℕ}{t : Tel n}{ty : U (suc n)}
      → (as bs : List (ElU (μ ty) t))
      → gapplyL (Dμ-inv (gdiffL as bs)) bs ≡ just as 
    Dμ-inv-sound [] [] = refl
    Dμ-inv-sound [] (b ∷ bs)
      rewrite ≟-U-refl (μ-hd b) = Dμ-inv-sound [] (μ-ch b ++ bs)
    Dμ-inv-sound (a ∷ as) [] 
      rewrite Dμ-inv-sound (μ-ch a ++ as) []
            | μ-close-resp-arity {hdA = μ-hd a} {chA = μ-ch a} {l = as} refl 
            = refl
    Dμ-inv-sound (a ∷ as) (b ∷ bs) 
      = gapply-⊔-inv
          {a = b ∷ bs} {b = a ∷ as}
          {d1 = Dμ-ins (p1 (μ-open b)) ∷ gdiffL (a ∷ as) (p2 (μ-open b) ++ bs)}
          {d2 = (Dμ-del (p1 (μ-open a)) ∷ gdiffL (p2 (μ-open a) ++ as) (b ∷ bs))
                ⊔μ (Dμ-dwn (gdiff (p1 (μ-open a)) (p1 (μ-open b))) ∷
                          gdiffL (p2 (μ-open a) ++ as) (p2 (μ-open b) ++ bs))}
          (mu-ins-L b) 
          (gapply-⊔-inv {a = b ∷ bs} {b = a ∷ as}
            {d1 = (Dμ-del (p1 (μ-open a)) ∷ gdiffL (p2 (μ-open a) ++ as) (b ∷ bs))} 
            {d2 = (Dμ-dwn (gdiff (p1 (μ-open a)) (p1 (μ-open b))) ∷
                          gdiffL (p2 (μ-open a) ++ as) (p2 (μ-open b) ++ bs))} 
             (mu-del-L a) 
             (mu-down-L a b))
\end{code}
