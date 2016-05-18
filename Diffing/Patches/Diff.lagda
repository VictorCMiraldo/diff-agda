\begin{code}
open import Prelude
open import Prelude.Vector
open import Prelude.NatProperties
  using (m≢n-elim; suc-inj; +-comm)
open import Prelude.ListProperties
  using (length-++; length-map; non-empty; all-++;
         all-map; all-pi; all-⇒)
open import Data.List.All using (All)

open import CF
open import CF.Operations
  using (ar-dry; chv; μ-ar; Z; Z-for; fgt; plugv)
open import CF.Properties
  using (length-Z; ar-dry-0-lemma; fgt-ar-lemma;
         ◂-correct; Z-correct; plugv-correct)

open import Diffing.Patches.D
open import Diffing.Patches.Cost

module Diffing.Patches.Diff (Δ : Cost) where
  open Cost
  
  infixr 20 _⊓_
\end{code}

  Another way of writing the type of gdiff
  could be:

  gdiff : ElU × ElU ⇒ Patch

%<*gdiff-type>
\begin{code}
  gdiff-μ : {n : ℕ}{t : T n}{ty : U (suc n)} 
          → ElU (μ ty) t → ElU (μ ty) t → Patch (μ ty) t

  {-# TERMINATING #-}
  gdiff : {n : ℕ}{t : T n}{ty : U n} 
        → ElU ty t → ElU ty t → Patch ty t
\end{code}
%</gdiff-type>

%<*cost-def>
\begin{code}
  cost : {n : ℕ}{t : T n}{ty : U n} → Patch ty t → ℕ
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
  cost (D-μ-add ctx d) = cμ Δ ctx + cost d
  cost (D-μ-rmv ctx d) = cμ Δ ctx + cost d
  cost (D-μ-dwn x y hip d)
    = cost (gdiff x y) + vsum (vmap cost d)
    where
      vsum : {k : ℕ} → Vec ℕ k → ℕ
      vsum []       = 0
      vsum (x ∷ xs) = x + vsum xs
\end{code}
%</cost-def>

%<*lub-def>
\begin{code}
  _⊓_ : {n : ℕ}{t : T n}{ty : U n}
      → Patch ty t → Patch ty t → Patch ty t
  _⊓_ {ty = ty} da db with cost da ≤?-ℕ cost db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lub-def>

%<*lub-def>
\begin{code}
  ⊓* : {n : ℕ}{t : T n}{ty : U n}
      → Patch ty t × List (Patch ty t) → Patch ty t
  ⊓* (p , [])    = p
  ⊓* (p , x ∷ l) = p ⊓ (⊓* (x , l))
\end{code}
%</lub-def>

%<*gdiff-def>
\begin{code}
  gdiff {ty = var} (top a) (top b)
    = D-top (gdiff a b)
  gdiff {ty = wk u} (pop a) (pop b)
    = D-pop (gdiff a b)
  gdiff {ty = def F x} (red a) (red b)
    = D-def (gdiff a b)
  gdiff {ty = u1} unit unit
    = D-unit
  gdiff {ty = ty ⊗ tv} (ay , av) (by , bv) 
    = D-pair (gdiff ay by) (gdiff av bv)
  gdiff {ty = ty ⊕ tv} (inl ay) (inl by)
    = D-inl (gdiff ay by)
  gdiff {ty = ty ⊕ tv} (inr av) (inr bv)
    = D-inr (gdiff av bv)
  gdiff {ty = ty ⊕ tv} (inl ay) (inr bv)
    = D-setl ay bv
  gdiff {ty = ty ⊕ tv} (inr av) (inl by)
    = D-setr av by
  gdiff {ty = μ ty} a b = gdiff-μ a b
\end{code}
%</gdiff-def>
\begin{code}
  gdiff-μ-rmv gdiff-μ-add
    : {n : ℕ}{t : T n}{ty : U (suc n)} 
    → ElU (μ ty) t → ElU (μ ty) t
    → List (Patch (μ ty) t)

  gdiff-μ-rmv (mu a) b
    = map (λ c → D-μ-rmv (p1 c) (gdiff (unpop (p2 c)) b)) (Z 0 a)

  gdiff-μ-add a (mu b)
    = map (λ c → D-μ-add (p1 c) (gdiff a (unpop (p2 c)))) (Z 0 b)

  gdiff-μ-dwn
    : {n : ℕ}{t : T n}{ty : U (suc n)} 
    → (a b : ElU (μ ty) t) → μ-ar a ≡ μ-ar b
    → Patch (μ ty) t
  gdiff-μ-dwn (mu a) (mu b) hip
    = D-μ-dwn (fgt 0 a) (fgt 0 b) hip 
              (vmap (λ { (pop x , pop y) → gdiff x y })
                    (vzip hip (chv 0 a) (chv 0 b)))
  
\end{code}
\begin{code}
  ctx-μ-add-rmv-nonempty
    : {n : ℕ}{t : T n}{ty : U (suc n)}
    → (a b : ElU (μ ty) t)(hip : μ-ar a ≡ μ-ar b → ⊥)
    → ∃ (λ n → suc n ≡ length (gdiff-μ-add a b ++ gdiff-μ-rmv a b))
  ctx-μ-add-rmv-nonempty (mu a) (mu b) hip
    with m≢n-elim (μ-ar (mu a)) (μ-ar (mu b)) hip
  ...| (k , i2 prfB)
     = k + length (gdiff-μ-rmv (mu a) (mu b))
     , (sym (trans (length-++ (gdiff-μ-add (mu a) (mu b)))
             ( (cong (λ P → P + length (gdiff-μ-rmv (mu a) (mu b)))
                      (trans (length-map _ (Z 0 b))
                      (trans (length-Z 0 b)
                      (trans (ar-dry-0-lemma b)
                      (trans (fgt-ar-lemma 0 b) prfB))))) )))
  ...| (k , i1 prfA)
     = k + length (gdiff-μ-add (mu a) (mu b))
     , (sym (trans (length-++ (gdiff-μ-add (mu a) (mu b)))
            (trans (+-comm (length (gdiff-μ-add (mu a) (mu b)))
                           (length (gdiff-μ-rmv (mu a) (mu b))))
             ( (cong (λ P → P + length (gdiff-μ-add (mu a) (mu b)))
                      (trans (length-map _ (Z 0 a))
                      (trans (length-Z 0 a)
                      (trans (ar-dry-0-lemma a)
                      (trans (fgt-ar-lemma 0 a) prfA))))) ))))
\end{code}
%<*gdiff-mu-def>
\begin{code}
  gdiff-μ a b with μ-ar a ≟-ℕ μ-ar b
  ...| no  p
     = ⊓* (non-empty (gdiff-μ-add a b ++ gdiff-μ-rmv a b) (ctx-μ-add-rmv-nonempty a b p))
  ...| yes p
     = ⊓* (gdiff-μ-dwn a b p , gdiff-μ-add a b ++ gdiff-μ-rmv a b)
\end{code}
%</gdiff-mu-def>

\begin{code}
  ⊓-elim : {n : ℕ}{t : T n}{ty : U n}
         → (P : Patch ty t → Set)
         → (p q : Patch ty t)
         → P p → P q
         → P (p ⊓ q)
  ⊓-elim P p q hp hq
    with cost p ≤?-ℕ cost q
  ...| yes _ = hp
  ...| no  _ = hq

  ⊓*-elim : {n : ℕ}{t : T n}{ty : U n}
          → (P : Patch ty t → Set)
          → (dl : Patch ty t × List (Patch ty t))
          → P (p1 dl) → All P (p2 dl)
          → P (⊓* dl)
  ⊓*-elim P (d , []) pHD pTL = pHD
  ⊓*-elim P (d , x ∷ dl) pHD (pX All.∷ pDL)
    = ⊓-elim P d (⊓* (x , dl)) pHD (⊓*-elim P (x , dl) pX pDL)

  ⊓*-elim-non-empty
    : {n : ℕ}{t : T n}{ty : U n}
    → (P : Patch ty t → Set)
    → (dl : List (Patch ty t))
    → (hip : ∃ (λ n → suc n ≡ length dl))
    → All P dl
    → P (⊓* (non-empty dl hip))
  ⊓*-elim-non-empty P [] (_ , ()) prf 
  ⊓*-elim-non-empty P (x ∷ dl) hip (px All.∷ pdl)
    = ⊓*-elim P (x , dl) px pdl
\end{code}

\begin{code}
  mutual
    gdiff-μ-add-src
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (x y : ElU ty (μ ty ∷ t))
      → All (λ P → D-src P ≡ mu x) (gdiff-μ-add (mu x) (mu y))
    gdiff-μ-add-src x y = all-map (Z 0 y)
                          (all-pi (λ a → gdiff-src-lemma (mu x) (unpop (p2 a))) (Z 0 y))


    gdiff-μ-rmv-src-1
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (x y : ElU ty (μ ty ∷ t))
      → (ctx : Ctx 0 ty (μ ty ∷ t) × ElU (wk (μ ty)) (μ ty ∷ t))
      → Z-for x ctx
      → D-src (D-μ-rmv (p1 ctx) (gdiff (unpop (p2 ctx)) (mu y)))
      ≡ mu x
    gdiff-μ-rmv-src-1 x y (ctx , pop a) hip
      rewrite gdiff-src-lemma a (mu y)
            = cong mu hip

    gdiff-μ-rmv-src
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (x y : ElU ty (μ ty ∷ t))
      → All (λ P → D-src P ≡ mu x) (gdiff-μ-rmv (mu x) (mu y))
    gdiff-μ-rmv-src x y
      = all-map (Z 0 x)
       (all-⇒ (Z 0 x) (Z-correct 0 x) (gdiff-μ-rmv-src-1 x y))


    gdiff-μ-dwn-src
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (x y : ElU (μ ty) t)
      → (hip : μ-ar x ≡ μ-ar y)
      → D-src (gdiff-μ-dwn x y hip) ≡ x
    gdiff-μ-dwn-src {ty = ty} (mu x) (mu y) hip
      = trans (cong (λ P → mu (plugv 0 (fgt 0 x) P))
                    (vmap-compose (vzip hip (chv 0 x) (chv 0 y))))
       (trans (cong (λ P → mu (plugv 0 (fgt 0 x) (vmap P (vzip hip (chv 0 x) (chv 0 y)))))
                    (fun-ext {g = p1}
                      (λ { (pop x1 , pop x2) → (cong pop (gdiff-src-lemma x1 x2)) })))
       (trans (cong (λ P → mu (plugv 0 (fgt 0 x) P)) (vzip-elim-p1 (chv 0 x) (chv 0 y) {hip}))
              (cong mu (sym (plugv-correct 0 x)))))
            

    {-# TERMINATING #-}
    gdiff-src-lemma
      : {n : ℕ}{t : T n}{ty : U n}
      → (x y : ElU ty t)
      → D-src (gdiff x y) ≡ x
    gdiff-src-lemma unit unit = refl
    gdiff-src-lemma (inl x) (inl y) = cong inl (gdiff-src-lemma x y)
    gdiff-src-lemma (inl x) (inr y) = refl
    gdiff-src-lemma (inr x) (inl y) = refl
    gdiff-src-lemma (inr x) (inr y) = cong inr (gdiff-src-lemma x y)
    gdiff-src-lemma (x1 , x2) (y1 , y2)
      = cong₂ _,_ (gdiff-src-lemma x1 y1) (gdiff-src-lemma x2 y2)
    gdiff-src-lemma (top x) (top y) = cong top (gdiff-src-lemma x y)
    gdiff-src-lemma (pop x) (pop y) = cong pop (gdiff-src-lemma x y)
    gdiff-src-lemma (mu x) (mu y)
      with μ-ar (mu x) ≟-ℕ μ-ar (mu y)
    ...| no  p = ⊓*-elim-non-empty (λ P → D-src P ≡ mu x)
               (gdiff-μ-add (mu x) (mu y) ++ gdiff-μ-rmv (mu x) (mu y))
               (ctx-μ-add-rmv-nonempty (mu x) (mu y) p)
               (all-++ 
                  (gdiff-μ-add (mu x) (mu y))
                  (gdiff-μ-add-src x y)
                  (gdiff-μ-rmv-src x y))
    ...| yes p
        = ⊓*-elim (λ P → D-src P ≡ mu x)
          (gdiff-μ-dwn (mu x) (mu y) p , gdiff-μ-add (mu x) (mu y) ++ gdiff-μ-rmv (mu x) (mu y))
          (gdiff-μ-dwn-src (mu x) (mu y) p)
          (all-++ 
            (gdiff-μ-add (mu x) (mu y))
            (gdiff-μ-add-src x y)
            (gdiff-μ-rmv-src x y))
    gdiff-src-lemma (red x₁) (red y) = cong red (gdiff-src-lemma x₁ y)
\end{code}

\begin{code}
  mutual
    gdiff-μ-rmv-dst
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (x y : ElU ty (μ ty ∷ t))
      → All (λ P → D-dst P ≡ mu y) (gdiff-μ-rmv (mu x) (mu y))
    gdiff-μ-rmv-dst x y = all-map (Z 0 x)
                          (all-pi (λ a → gdiff-dst-lemma (unpop (p2 a)) (mu y)) (Z 0 x))


    gdiff-μ-add-dst-1
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (x y : ElU ty (μ ty ∷ t))
      → (ctx : Ctx 0 ty (μ ty ∷ t) × ElU (wk (μ ty)) (μ ty ∷ t))
      → Z-for y ctx
      → D-dst (D-μ-add (p1 ctx) (gdiff (mu x) (unpop (p2 ctx))))
      ≡ mu y
    gdiff-μ-add-dst-1 x y (ctx , pop a) hip
      rewrite gdiff-dst-lemma (mu x) a
        = cong mu hip

    gdiff-μ-add-dst
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (x y : ElU ty (μ ty ∷ t))
      → All (λ P → D-dst P ≡ mu y) (gdiff-μ-add (mu x) (mu y))
    gdiff-μ-add-dst x y
      = all-map (Z 0 y) (all-⇒ (Z 0 y) (Z-correct 0 y) (gdiff-μ-add-dst-1 x y)) 


    gdiff-μ-dwn-dst
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (x y : ElU (μ ty) t)
      → (hip : μ-ar x ≡ μ-ar y)
      → D-dst (gdiff-μ-dwn x y hip) ≡ y
    gdiff-μ-dwn-dst {ty = ty} (mu x) (mu y) hip
      with μ-ar (mu x) ≟-ℕ μ-ar (mu y)
    ...| no abs  = ⊥-elim (abs hip)
    ...| yes prf = {!!}


    {-# TERMINATING #-}
    gdiff-dst-lemma
      : {n : ℕ}{t : T n}{ty : U n}
      → (x y : ElU ty t)
      → D-dst (gdiff x y) ≡ y
    gdiff-dst-lemma = {!!}
\end{code}
