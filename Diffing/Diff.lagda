\begin{code}
open import Prelude hiding (_⊔_)
open import Prelude.ListProperties
  using (lhead-elim; map-lemma; lsplit-elim)
open import Diffing.Universe
open import CF.Properties.Base
  using (plug-correct; plug-spec-fgt; plug-spec-ch)
open import CF.Properties.Mu
  using (μ-close-correct; μ-ar-close-lemma; μ-open-ar-lemma)

open import Diffing.Patches.Cost
open import Diffing.Patches.Properties.WellFormed

module Diffing.Diff (Δ : Cost) where

  open import Diffing.Patches.D
\end{code}

  The cost of a diff depends only on the
  cost associated to coproducts and to
  fixpoints.

\begin{code}
  mutual
    {-# TERMINATING #-}
\end{code}
%<*cost-type>
\begin{code}
    cost : {n : ℕ}{t : T n}{ty : U n} → Patch t ty → ℕ
\end{code}
%</cost-type>
\begin{code}
    costL : {n : ℕ}{t : T n}{ty : U (suc n)} 
          → Patchμ t ty → ℕ
    costL [] = 0
    costL (p ∷ ps) = costμ p + costL ps
\end{code}
%<*cost-def>
\begin{code}
    cost (D-A ())
    cost  D-unit         = 0
    cost (D-inl d)       = cost d
    cost (D-inr d)       = cost d
    cost (D-setl xa xb)  = C⊕ Δ xa xb
    cost (D-setr xa xb)  = C⊕ Δ xa xb
    cost (D-pair da db)  = cost da + cost db
    cost (D-def d)       = cost d
    cost (D-top d)       = cost d
    cost (D-pop d)       = cost d
    cost (D-mu l)        = costL l
\end{code}
%</cost-def>
%<*costmu-type>
\begin{code}
    costμ : {n : ℕ}{t : T n}{ty : U (suc n)} 
          → Dμ ⊥ₚ t ty → ℕ
\end{code}
%</costmu-type>
%<*costmu-def>
\begin{code}
    costμ (Dμ-A ())
    costμ (Dμ-ins x)  = Cμ Δ x
    costμ (Dμ-del x)  = Cμ Δ x
    costμ (Dμ-dwn x)  = cost x
\end{code}
%</costmu-def>

  Given two patches, we can now select the one
  with the minimum cost.

\begin{code}
  infixr 20 _⊔_
  infixr 20 _⊔μ_
\end{code}

%<*lub-def>
\begin{code}
  _⊔_ : {n : ℕ}{t : T n}{ty : U n}
      → Patch t ty → Patch t ty → Patch t ty
  _⊔_ {ty = ty} da db with cost da ≤?-ℕ cost db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lub-def>

%<*lubmu-def>
\begin{code}
  _⊔μ_ : {n : ℕ}{t : T n}{ty : U (suc n)}
      → Patchμ t ty → Patchμ t ty → Patchμ t ty
  _⊔μ_ da db with costL da ≤?-ℕ costL db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lubmu-def>

\begin{code}
  ⊔μ-elim : {n : ℕ}{t : T n}{ty : U (suc n)}{P : Patchμ t ty → Set}
          → (da db : Patchμ t ty)
          → P da → P db → P (da ⊔μ db)
  ⊔μ-elim da db pda pdb with costL da ≤?-ℕ costL db
  ...| yes _ = pda
  ...| no  _ = pdb
\end{code}

\begin{code}
  ⊔μ-elim-3 : {n : ℕ}{t : T n}{ty : U (suc n)}{P : Patchμ t ty → Set}
            → (da db dc : Patchμ t ty)
            → P da → P db → P dc → P (da ⊔μ db ⊔μ dc)
  ⊔μ-elim-3 da db dc pda pdb pdc
    = ⊔μ-elim da (db ⊔μ dc) pda (⊔μ-elim db dc pdb pdc)
\end{code}

  And finally proceed to the diffing algorithm

\begin{code}
  mutual
    {-# TERMINATING #-}
\end{code}
%<*gdiff-def>
\begin{code}
    gdiff : {n : ℕ}{t : T n}{ty : U n} 
          → ElU ty t → ElU ty t → Patch t ty
    gdiff {ty = u1}       unit unit 
      = D-unit
    gdiff {ty = var}      (top a)    (top b)    
      = D-top (gdiff a b)
    gdiff {ty = wk u}     (pop a)    (pop b)  
      = D-pop (gdiff a b)
    gdiff {ty = def F x}  (red a)    (red b) 
      = D-def (gdiff a b)
    gdiff {ty = ty ⊗ tv}  (ay , av)  (by , bv) 
      = D-pair (gdiff ay by) (gdiff av bv)
    gdiff {ty = ty ⊕ tv}  (inl ay)   (inl by) 
      = D-inl (gdiff ay by)
    gdiff {ty = ty ⊕ tv}  (inr av)   (inr bv) 
      = D-inr (gdiff av bv)
    gdiff {ty = ty ⊕ tv}  (inl ay)   (inr bv) 
      = D-setl ay bv
    gdiff {ty = ty ⊕ tv}  (inr av)   (inl by) 
      = D-setr av by
    gdiff {ty = μ ty}     a          b 
      = D-mu (gdiffL (a ∷ []) (b ∷ []))
\end{code}
%</gdiff-def>

%<*gdiffL-def>
\begin{code}
    gdiffL : {n : ℕ}{t : T n}{ty : U (suc n)} 
           → List (ElU (μ ty) t) → List (ElU (μ ty) t) → Patchμ t ty
    gdiffL [] [] = []
    gdiffL [] (y ∷ ys) 
      = Dμ-ins (μ-hd y) ∷ (gdiffL [] (μ-ch y ++ ys)) 
    gdiffL (x ∷ xs) [] 
      = Dμ-del (μ-hd x) ∷ (gdiffL (μ-ch x ++ xs) [])
    gdiffL (x ∷ xs) (y ∷ ys) 
      = let
          hdX , chX = μ-open x
          hdY , chY = μ-open y
          d1 = Dμ-ins hdY ∷ (gdiffL (x ∷ xs) (chY ++ ys))
          d2 = Dμ-del hdX ∷ (gdiffL (chX ++ xs) (y ∷ ys))
          d3 = Dμ-dwn (gdiff hdX hdY) ∷ (gdiffL (chX ++ xs) (chY ++ ys))
       in d1 ⊔μ d2 ⊔μ d3
\end{code}
%</gdiffL-def>
begin{code}
    gdiffL : {n : ℕ}{t : T n}{ty : U (suc n)} 
           → List (ElU (μ ty) t) → List (ElU (μ ty) t) → Patchμ t ty
    gdiffL [] [] = []
    gdiffL [] (y ∷ ys) with μ-open y
    ...| hdY , chY = Dμ-ins hdY ∷ (gdiffL [] (chY ++ ys)) 
    gdiffL (x ∷ xs) [] with μ-open x
    ...| hdX , chX = Dμ-del hdX ∷ (gdiffL (chX ++ xs) [])
    gdiffL (x ∷ xs) (y ∷ ys) 
      = let
          hdX , chX = μ-open x
          hdY , chY = μ-open y
          d1 = Dμ-ins hdY ∷ (gdiffL (x ∷ xs) (chY ++ ys))
          d2 = Dμ-del hdX ∷ (gdiffL (chX ++ xs) (y ∷ ys))
          d3 = Dμ-dwn (gdiff hdX hdY) ∷ (gdiffL (chX ++ xs) (chY ++ ys))
       in d1 ⊔μ d2 ⊔μ d3
end{code}

  Now some nice lemmas about diffs.

\begin{code}
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


\end{code}

  Hence, gdiff returns always a well-founded patch.

\begin{code}
  gdiff-wf : {n : ℕ}{t : T n}{ty : U n}
           → (x y : ElU ty t)
           → WF (gdiff x y)
  gdiff-wf x y = ((x , y) , gdiff-src-lemma x y , gdiff-dst-lemma x y)
\end{code}
