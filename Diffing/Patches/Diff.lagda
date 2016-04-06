\begin{code}
{-# OPTIONS --rewriting #-}
open import Prelude
open import Diffing.Universe
open import Diffing.Utils.Vector
open import Diffing.Patches.Diff.Cost
open import Diffing.Patches.Diff.D

module Diffing.Patches.Diff (Δ : Cost)
  where

  open Cost
\end{code}

            Diffing
  ===========================

  We start by introducing a "generic" notion of cost. 

\begin{code}
  infixr 20 _⊓_
  infixr 20 _⊓μ_
\end{code}

%<*gdiff-type>
\begin{code}
  {-# TERMINATING #-}
  gdiff : {n : ℕ}{t : T n}{ty : U n} 
        → ElU ty t → ElU ty t → Patch t ty
\end{code}
%</gdiff-type>

\begin{code}
  mutual
    {-# TERMINATING #-}
\end{code}
%<*cost-def>
\begin{code}
    cost : {n : ℕ}{t : T n}{ty : U n} → Patch t ty → ℕ
    cost (D-A ())
    cost D-unit         = 0
    cost (D-inl d)      = cost d
    cost (D-inr d)      = cost d
    cost (D-setl xa xb) = 1 + c⊕ Δ xa xb
    cost (D-setr xa xb) = 1 + c⊕ Δ xb xa
    cost (D-pair da db) = cost da + cost db
    cost (D-def d) = cost d
    cost (D-top d) = cost d
    cost (D-pop d) = cost d
    cost (D-mu l)  = costμ l

    costμ : {n i j : ℕ}{t : T n}{ty : U (suc n)} → Dμ ⊥ₚ t ty i j → ℕ
    costμ (Dμ-A () d)  
    costμ (Dμ-ins x d) = 1 + cμ Δ x + costμ d
    costμ (Dμ-del x d) = 1 + cμ Δ x + costμ d
    costμ (Dμ-dwn x y d) = cost (gdiff x y) + costμ d
    costμ Dμ-end = 0
\end{code}
%</cost-def>

%<*lub-def>
\begin{code}
  _⊓_ : {n : ℕ}{t : T n}{ty : U n}
      → Patch t ty → Patch t ty → Patch t ty
  _⊓_ {ty = ty} da db with cost da ≤?-ℕ cost db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lub-def>

%<*lubmu-def>
\begin{code}
  _⊓μ_ : {n i j : ℕ}{t : T n}{ty : U (suc n)}
      → Dμ ⊥ₚ t ty i j → Dμ ⊥ₚ t ty i j → Dμ ⊥ₚ t ty i j
  _⊓μ_ da db with costμ da ≤?-ℕ costμ db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lubmu-def>

\begin{code}
  ⊓μ-elim : {n i j : ℕ}{t : T n}{ty : U (suc n)}{P : {i j : ℕ} → Dμ ⊥ₚ t ty i j → Set}
          → (da db : Dμ ⊥ₚ t ty i j)
          → P da → P db → P (da ⊓μ db)
  ⊓μ-elim da db pda pdb with costμ da ≤?-ℕ costμ db
  ...| yes _ = pda
  ...| no  _ = pdb

  ⊓μ-elim3 : {n i j : ℕ}{t : T n}{ty : U (suc n)}{P : {i j : ℕ} → Dμ ⊥ₚ t ty i j → Set}
           → (da db dc : Dμ ⊥ₚ t ty i j)
           → P da → P db → P dc → P (da ⊓μ (db ⊓μ dc))
  ⊓μ-elim3 {P = P} da db dc pda pdb pdc
    = ⊓μ-elim {P = P} da (db ⊓μ dc) pda (
        ⊓μ-elim {P = P} db dc pdb pdc)
      

  ⊓μ-elim-imp 
    : {n i j : ℕ}{t : T n}{ty : U (suc n)}{P : {i j : ℕ} → Dμ ⊥ₚ t ty i j → Set}
      {da db : Dμ ⊥ₚ t ty i j}
    → P da → P db → P (da ⊓μ db)
  ⊓μ-elim-imp {P = P} {da} {db} pda pdb = ⊓μ-elim {P = P} da db pda pdb
\end{code}

%<*gdiffL-type>
\begin{code}
  gdiffL : {n : ℕ}{t : T n}{ty : U (suc n)} 
         → (xs ys : List (ElU (μ ty) t)) → Dμ ⊥ₚ t ty (length xs) (length ys)
\end{code}
%</gdiffL-type>

  Before the actual diffing algorithm, we still need
  to populate our bag of tricks.

  Now we can define auxiliar functions for computing recursive diffs
  AND taking care of their indicies.

\begin{code}
  {-# REWRITE μ-lal-sym #-}
  gdiffL-ins : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (length xs) (suc (length ys))
  gdiffL-ins y xs ys = Dμ-ins (μ-hd y) (gdiffL xs (μ-ch y ++ ys))

  gdiffL-del : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (suc (length xs)) (length ys)
  gdiffL-del x xs ys = Dμ-del (μ-hd x) (gdiffL (μ-ch x ++ xs) ys)

  gdiffL-dwn : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (suc (length xs)) (suc (length ys))
  gdiffL-dwn x y xs ys 
    = Dμ-dwn (μ-hd x) (μ-hd y) (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys))
\end{code}

  Finally, the actual diffing algorithm.

%<*gdiff-def>
\begin{code}
  gdiff {ty = var} (top a) (top b)    = D-top (gdiff a b)
  gdiff {ty = wk u} (pop a) (pop b)  = D-pop (gdiff a b)
  gdiff {ty = def F x} (red a) (red b) = D-def (gdiff a b)
  gdiff {ty = u1} unit unit = D-unit
  gdiff {ty = ty ⊗ tv} (ay , av) (by , bv) 
    = D-pair (gdiff ay by) (gdiff av bv)
  gdiff {ty = ty ⊕ tv} (inl ay) (inl by) = D-inl (gdiff ay by)
  gdiff {ty = ty ⊕ tv} (inr av) (inr bv) = D-inr (gdiff av bv)
  gdiff {ty = ty ⊕ tv} (inl ay) (inr bv) = D-setl ay bv
  gdiff {ty = ty ⊕ tv} (inr av) (inl by) = D-setr av by
  gdiff {ty = μ ty} a b = D-mu (gdiffL (a ∷ []) (b ∷ []))
\end{code}
%</gdiff-def>
%<*gdiffL-def>
\begin{code}
  gdiffL [] [] = Dμ-end
  gdiffL [] (y ∷ ys) = gdiffL-ins y [] ys
  gdiffL (x ∷ xs) [] = gdiffL-del x xs [] 
  gdiffL (x ∷ xs) (y ∷ ys) 
    =  gdiffL-ins y (x ∷ xs) ys 
    ⊓μ gdiffL-del x xs (y ∷ ys)
    ⊓μ gdiffL-dwn x y xs ys
\end{code}
%</gdiffL-def>

  Now, we can prove that D-src and D-dst are projections of a diff.

\begin{code}
  {-# TERMINATING #-}
\end{code}
%<*gdiffL-src-lemma-type>
\begin{code}
  gdiffL-src-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
                  → (x y : List (ElU (μ ty) t))
                  → Dμ-srcv (gdiffL x y) ≡ vec x refl
\end{code}
%</gdiffL-src-lemma-type>
\begin{code}
  private
    src-del : {n : ℕ}{t : T n}{ty : U (suc n)}
            → (x : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
            → Dμ-srcv (gdiffL-del x xs ys) ≡ vec (x ∷ xs) refl
    src-del x xs ys rewrite gdiffL-src-lemma (μ-ch x ++ xs) ys
      with vsplit-elim (μ-ch x) xs {p = μ-open-ar-++-lemma x xs} 
              {q₁ = μ-open-ar-lemma x } {q₂ = refl} 
    ...| prf rewrite ≡-pi (μ-open-ar-++-lemma x xs) refl | prf 
      = cong (λ P → P ∷ vec xs refl) (μ-plugv-correct x)

    src-dwn : {n : ℕ}{t : T n}{ty : U (suc n)}
            → (x y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
            → Dμ-srcv (gdiffL-dwn x y xs ys) ≡ vec (x ∷ xs) refl
    src-dwn x y xs ys rewrite gdiffL-src-lemma (μ-ch x ++ xs) (μ-ch y ++ ys)
      with vsplit-elim (μ-ch x) xs {p = μ-open-ar-++-lemma x xs} 
              {q₁ = μ-open-ar-lemma x } {q₂ = refl} 
    ...| prf rewrite ≡-pi (μ-open-ar-++-lemma x xs) refl | prf 
      = cong (λ P → P ∷ vec xs refl) (μ-plugv-correct x)
\end{code}
%<*gdiffL-src-lemma-def>
\begin{code}
  gdiffL-src-lemma [] []       = refl
  gdiffL-src-lemma [] (y ∷ ys) = gdiffL-src-lemma [] (μ-ch y ++ ys)
  gdiffL-src-lemma (x ∷ xs) [] = src-del x xs []
  gdiffL-src-lemma (x ∷ xs) (y ∷ ys) 
    = toList-vec-≡ (x ∷ xs) _
        (⊓μ-elim3 {P = λ p → toList (Dμ-srcv p) ≡ x ∷ xs}
         (gdiffL-ins y (x ∷ xs) ys) 
         (gdiffL-del x xs (y ∷ ys))
         (gdiffL-dwn x y xs ys) 
         (trans (cong toList (gdiffL-src-lemma (x ∷ xs) (μ-ch y ++ ys))) 
                (cong (_∷_ x) (toList-vec xs))) 
         (trans (cong toList (src-del x xs (y ∷ ys))) 
                (cong (_∷_ x) (toList-vec xs))) 
         (trans (cong toList (src-dwn x y xs ys)) 
                (cong (_∷_ x) (toList-vec xs))))
\end{code}
%</gdiffL-src-lemma-def>

%<*gdiff-src-lemma-type>
\begin{code}
  gdiff-src-lemma : {n : ℕ}{t : T n}{ty : U n}
                  → (x y : ElU ty t)
                  → D-src (gdiff x y) ≡ x
\end{code}
%</gdiff-src-lemma-type>
%<*gdiff-src-lemma-def>
\begin{code}
  gdiff-src-lemma unit unit = refl
  gdiff-src-lemma (inl x) (inl y) = cong inl (gdiff-src-lemma x y)
  gdiff-src-lemma (inl x) (inr y) = refl
  gdiff-src-lemma (inr x) (inl y) = refl
  gdiff-src-lemma (inr x) (inr y) = cong inr (gdiff-src-lemma x y)
  gdiff-src-lemma (x1 , x2) (y1 , y2) 
    = cong₂ _,_ (gdiff-src-lemma x1 y1) (gdiff-src-lemma x2 y2)
  gdiff-src-lemma (top x) (top y) = cong top (gdiff-src-lemma x y)
  gdiff-src-lemma (pop x) (pop y) = cong pop (gdiff-src-lemma x y)
  gdiff-src-lemma (red x) (red y) = cong red (gdiff-src-lemma x y)
  gdiff-src-lemma (mu x) (mu y) 
    = cong head (gdiffL-src-lemma (mu x ∷ []) (mu y ∷ []))
\end{code}
%</gdiff-src-lemma-def>

\begin{code}
  {-# TERMINATING #-}
\end{code}
%<*gdiffL-dst-lemma-type>
\begin{code}
  gdiffL-dst-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
                  → (x y : List (ElU (μ ty) t))
                  → Dμ-dstv (gdiffL x y) ≡ vec y refl
\end{code}
%</gdiffL-dst-lemma-type>
\begin{code}
  private
    dst-ins : {n : ℕ}{t : T n}{ty : U (suc n)}
            → (y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
            → Dμ-dstv (gdiffL-ins y xs ys) ≡ vec (y ∷ ys) refl
    dst-ins y xs ys rewrite gdiffL-dst-lemma xs (μ-ch y ++ ys)
      with vsplit-elim (μ-ch y) ys {p = μ-open-ar-++-lemma y ys} 
              {q₁ = μ-open-ar-lemma y} {q₂ = refl} 
    ...| prf rewrite ≡-pi (μ-open-ar-++-lemma y ys) refl | prf
       = cong (λ P → P ∷ vec ys refl) (μ-plugv-correct y)

    dst-dwn : {n : ℕ}{t : T n}{ty : U (suc n)}
            → (x y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
            → Dμ-dstv (gdiffL-dwn x y xs ys) ≡ vec (y ∷ ys) refl
    dst-dwn x y xs ys rewrite gdiffL-dst-lemma (μ-ch x ++ xs) (μ-ch y ++ ys)
      with vsplit-elim (μ-ch y) ys {p = μ-open-ar-++-lemma y ys} 
              {q₁ = μ-open-ar-lemma y} {q₂ = refl} 
    ...| prf rewrite ≡-pi (μ-open-ar-++-lemma y ys) refl | prf 
      = cong (λ P → P ∷ vec ys refl) (μ-plugv-correct y)
\end{code}
%<*gdiffL-dst-lemma-def>
\begin{code}
  gdiffL-dst-lemma [] []       = refl
  gdiffL-dst-lemma [] (y ∷ ys) = dst-ins y [] ys
  gdiffL-dst-lemma (x ∷ xs) [] = gdiffL-dst-lemma (μ-ch x ++ xs) []
  gdiffL-dst-lemma (x ∷ xs) (y ∷ ys) 
    = toList-vec-≡ (y ∷ ys) _
        (⊓μ-elim3 {P = λ p → toList (Dμ-dstv p) ≡ y ∷ ys}
         (gdiffL-ins y (x ∷ xs) ys) 
         (gdiffL-del x xs (y ∷ ys))
         (gdiffL-dwn x y xs ys) 
         (trans (cong toList (dst-ins y (x ∷ xs) ys)) 
                (cong (_∷_ y) (toList-vec ys)))
         (trans (cong toList (gdiffL-dst-lemma (μ-ch x ++ xs) (y ∷ ys))) 
                (cong (_∷_ y) (toList-vec ys))) 
         (trans (cong toList (dst-dwn x y xs ys)) 
                (cong (_∷_ y) (toList-vec ys))))
\end{code}
%</gdiffL-dst-lemma-def>

%<*gdiff-dst-lemma-type>
\begin{code}
  gdiff-dst-lemma : {n : ℕ}{t : T n}{ty : U n}
                  → (x y : ElU ty t)
                  → D-dst (gdiff x y) ≡ y
\end{code}
%</gdiff-dst-lemma-type>
%<*gdiff-dst-lemma-def>
\begin{code}
  gdiff-dst-lemma unit unit = refl
  gdiff-dst-lemma (inl x) (inl y) = cong inl (gdiff-dst-lemma x y)
  gdiff-dst-lemma (inl x) (inr y) = refl
  gdiff-dst-lemma (inr x) (inl y) = refl
  gdiff-dst-lemma (inr x) (inr y) = cong inr (gdiff-dst-lemma x y)
  gdiff-dst-lemma (x1 , x2) (y1 , y2) 
    = cong₂ _,_ (gdiff-dst-lemma x1 y1) (gdiff-dst-lemma x2 y2)
  gdiff-dst-lemma (top x) (top y) = cong top (gdiff-dst-lemma x y)
  gdiff-dst-lemma (pop x) (pop y) = cong pop (gdiff-dst-lemma x y)
  gdiff-dst-lemma (red x) (red y) = cong red (gdiff-dst-lemma x y)
  gdiff-dst-lemma (mu x) (mu y) 
    = cong head (gdiffL-dst-lemma (mu x ∷ []) (mu y ∷ []))
\end{code}
%</gdiff-dst-lemma-def>

  Ideally, we would like to prove the other side of the isomorphism;
  this is much trickier in Agda, though.

%<*src-dst-gdiff-lemma-type>
begin{code}
  src-dst-gdiff-lemma 
    : {n : ℕ}{t : T n}{ty : U n}(p : D ⊥ₚ t ty)
    → gdiff (D-src p) (D-dst p) ≡ p
end{code}
%</src-dst-gdiff-lemma-type>
%<*src-dst-gdiffL-lemma-type>
begin{code}
  src-dst-gdiffL-lemma 
    : {n i j : ℕ}{t : T n}{ty : U (suc n)}(p : Dμ ⊥ₚ t ty i j)
    → gdiffL (Dμ-src p) (Dμ-dst p) ≡ Dμ-unlink-nats p
end{code}
%</src-dst-gdiffL-lemma-type>
%<*src-dst-gdiffL-lemma-def>
begin{code}
  src-dst-gdiffL-lemma (Dμ-A () p)
  src-dst-gdiffL-lemma Dμ-end = refl
  src-dst-gdiffL-lemma (Dμ-dwn a b p) 
    = {!!}
  src-dst-gdiffL-lemma (Dμ-del a p) = {!h1 h2!}
  src-dst-gdiffL-lemma (Dμ-ins a p) = {!!}
end{code}
%</src-dst-gdiffL-lemma-def>
%<*src-dst-gdiff-lemma-def>
begin{code}
  src-dst-gdiff-lemma (D-A ())
  src-dst-gdiff-lemma D-unit = refl
  src-dst-gdiff-lemma (D-inl p) 
    rewrite src-dst-gdiff-lemma p = refl
  src-dst-gdiff-lemma (D-inr p) 
    rewrite src-dst-gdiff-lemma p = refl
  src-dst-gdiff-lemma (D-setl x y) 
    = refl
  src-dst-gdiff-lemma (D-setr x y) 
    = refl
  src-dst-gdiff-lemma (D-pair p q) 
    rewrite src-dst-gdiff-lemma p 
          | src-dst-gdiff-lemma q
          = refl
  src-dst-gdiff-lemma (D-mu x) 
    with Dμ-srcv x | inspect Dμ-srcv x | Dμ-dstv x | inspect Dμ-dstv x
  ...| mu y ∷ [] | [ R0 ] | mu y' ∷ [] | [ R1 ]
     = cong D-mu (src-dst-gdiffL-lemma {i = 1} {1} {!!})
  src-dst-gdiff-lemma (D-def p) = {!!}
  src-dst-gdiff-lemma (D-top p) = {!!}
  src-dst-gdiff-lemma (D-pop p) = {!!}
end{code}
%</src-dst-gdiff-lemma-def>
