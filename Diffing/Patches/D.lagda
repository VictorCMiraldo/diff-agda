\begin{code}
open import Prelude
open import Prelude.Vector
open import Diffing.CF-base

module Diffing.Patches.D where
\end{code}

  Here we define our Patch datatype and
  both projections: source and destination.

%<*natural-transformation-def>
\begin{code}
  infixr 3 _⇒_

  _⇒_ : (A : {n : ℕ} → U n → T n → Set)
      → (B : {n : ℕ} → U n → T n → Set)
      → Set
  A ⇒ B = {n : ℕ}{t : T n}{ty : U n} → A ty t → B ty t
\end{code}
%</natural-transformation-def>

\begin{code}
  mutual
\end{code}
%<*D-type>
\begin{code}
    data D (A : {n : ℕ} → U n → T n → Set) 
      : {n : ℕ} → U n → T n → Set where
\end{code}
%</D-type>
%<*D-A-def>
\begin{code}
      D-A    : {n : ℕ}{t : T n}{ty : U n} → A ty t → D A ty t
\end{code}
%</D-A-def>
%<*D-void-def>
\begin{code}
      D-unit : {n : ℕ}{t : T n} → D A u1 t
\end{code}
%</D-void-def>
%<*D-sum-def>
\begin{code}
      D-inl  : {n : ℕ}{t : T n}{a b : U n} 
             → D A a t → D A (a ⊕ b) t
      D-inr  : {n : ℕ}{t : T n}{a b : U n} 
             → D A b t → D A (a ⊕ b) t
      D-setl : {n : ℕ}{t : T n}{a b : U n} 
             → ElU a t → ElU b t → D A (a ⊕ b) t
      D-setr : {n : ℕ}{t : T n}{a b : U n} 
             → ElU b t → ElU a t → D A (a ⊕ b) t
\end{code}
%</D-sum-def>
%<*D-pair-def>
\begin{code}
      D-pair : {n : ℕ}{t : T n}{a b : U n} 
             → D A a t → D A b t → D A (a ⊗ b) t
\end{code}
%</D-pair-def>
%<*D-mu-dwn-def>
\begin{code}
      D-μ-dwn : {n k : ℕ}{t : T n}{a : U (suc n)}
              → (d : D A a (u1 ∷ t))
              → (hi : D-arᵢ 0 d ≡ k)
              → (ho : D-arₒ 0 d ≡ k)
              → Vec (D A (μ a) t) k → D A (μ a) t
\end{code}
%</D-mu-dwn-def>
%<*D-mu-add-rmv-def>
\begin{code}
      D-μ-add : {n : ℕ}{t : T n}{a : U (suc n)}
              → Ctx 0 a (μ a ∷ t) → D A (μ a) t → D A (μ a) t
      D-μ-rmv : {n : ℕ}{t : T n}{a : U (suc n)}
              → Ctx 0 a (μ a ∷ t) → D A (μ a) t → D A (μ a) t
\end{code}
%</D-mu-add-rmv-def>
%<*D-rest-def>
\begin{code}
      D-def : {n : ℕ}{t : T n}{F : U (suc n)}{x : U n} 
            → D A F (x ∷ t) → D A (def F x) t
      D-top : {n : ℕ}{t : T n}{a : U n}
            → D A a t → D A var (a ∷ t)
      D-pop : {n : ℕ}{t : T n}{a b : U n}
            → D A b t → D A (wk b) (a ∷ t) 
\end{code}
%</D-rest-def>

\begin{code}
    {-# TERMINATING #-}
    D-arᵢ D-arₒ
      : {A : {n : ℕ} → U n → T n → Set}
        {n : ℕ}{t : T n}{ty : U n}
      → ℕ → D A ty t → ℕ
\end{code}
\begin{code}
    D-arᵢ i (D-A x) = 0
    D-arᵢ i D-unit = 0
    D-arᵢ i (D-inl d) = D-arᵢ i d
    D-arᵢ i (D-inr d) = D-arᵢ i d
    D-arᵢ i (D-setl x y) = ar i x
    D-arᵢ i (D-setr x y) = ar i x
    D-arᵢ i (D-pair d p) = D-arᵢ i d + D-arᵢ i p
    D-arᵢ i (D-def d) = D-arᵢ (suc i) d
    D-arᵢ zero    (D-top d) = 1
    D-arᵢ (suc i) (D-top d) = D-arᵢ i d
    D-arᵢ zero    (D-pop d) = 0
    D-arᵢ (suc i) (D-pop d) = D-arᵢ i d
    D-arᵢ i (D-μ-dwn d hi ho x)
      = D-arᵢ (suc i) d + vsum (vmap (D-arᵢ i) x)
    D-arᵢ i (D-μ-add x d)
      = D-arᵢ i d
    D-arᵢ i (D-μ-rmv x d)
      = φ-ar (suc i) x + D-arᵢ i d

    D-arₒ i (D-A x) = 0
    D-arₒ i D-unit = 0
    D-arₒ i (D-inl d) = D-arₒ i d
    D-arₒ i (D-inr d) = D-arₒ i d
    D-arₒ i (D-setl x y) = ar i y
    D-arₒ i (D-setr x y) = ar i y
    D-arₒ i (D-pair d p) = D-arₒ i d + D-arₒ i p 
    D-arₒ i (D-def d) = D-arₒ (suc i) d
    D-arₒ zero (D-top d) = 1
    D-arₒ (suc i) (D-top d) = D-arₒ i d
    D-arₒ zero (D-pop d) = 0
    D-arₒ (suc i) (D-pop d) = D-arₒ i d
    D-arₒ i (D-μ-dwn d hi ho x)
      = D-arₒ (suc i) d + vsum (vmap (D-arₒ i) x)
    D-arₒ i (D-μ-add x d)
      = φ-ar (suc i) x + D-arₒ i d
    D-arₒ i (D-μ-rmv x d)
      = D-arₒ i d
\end{code}

%<*Patch-def>
\begin{code}
  ⊥ₚ : {n : ℕ} → U n → T n → Set
  ⊥ₚ {_} _ _ = ⊥

  Patch : {n : ℕ} → U n → T n → Set
  Patch ty t = D ⊥ₚ ty t
\end{code}
%</Patch-def>

\begin{code}
  mutual
\end{code}
%<*D-src-type>
\begin{code}
    {-# TERMINATING #-}
    D-src : {n : ℕ}{t : T n}{ty : U n}
          → Patch ty t → ElU ty t
\end{code}
%</D-src-type>
%<*D-ar-src-lemma-type>
\begin{code}
    D-ar-src-lemma
      : {n : ℕ}{t : T n}{ty : U n}
      → (i : ℕ)(p : Patch ty t)
      → D-arᵢ i p ≡ ar i (D-src p)
\end{code}
%</D-ar-src-lemma-type>
%<*D-src-def>
\begin{code}
    D-src (D-A ())
    D-src D-unit = unit
    D-src (D-inl d) = inl (D-src d)
    D-src (D-inr d) = inr (D-src d)
    D-src (D-setl x _) = inl x
    D-src (D-setr x _) = inr x
    D-src (D-pair d e) = D-src d , D-src e
    D-src (D-def d) = red (D-src d)
    D-src (D-top d) = top (D-src d)
    D-src (D-pop d) = pop (D-src d)
    D-src (D-μ-dwn p hi ho d)
      rewrite D-ar-src-lemma 0 p
      = mu (plugv 0 (D-src p) (vmap (pop ∘ D-src) (vec-reindx (sym hi) d)))
    D-src (D-μ-add ctx d)
      = D-src d
    D-src (D-μ-rmv ctx d)
      = mu (ctx ◂ pop (D-src d))
\end{code}
%</D-src-def>

\begin{code}
    D-ar-src-lemma i (D-A ())
    D-ar-src-lemma i D-unit = refl
    D-ar-src-lemma i (D-inl p) = D-ar-src-lemma i p
    D-ar-src-lemma i (D-inr p) = D-ar-src-lemma i p
    D-ar-src-lemma i (D-setl x x₁) = refl
    D-ar-src-lemma i (D-setr x x₁) = refl
    D-ar-src-lemma i (D-pair p p₁) = cong₂ _+_ (D-ar-src-lemma i p) (D-ar-src-lemma i p₁)
    D-ar-src-lemma i (D-def p) = D-ar-src-lemma (suc i) p
    D-ar-src-lemma zero (D-top p) = refl
    D-ar-src-lemma (suc i) (D-top p) = D-ar-src-lemma i p
    D-ar-src-lemma zero (D-pop p) = refl
    D-ar-src-lemma (suc i) (D-pop p) = D-ar-src-lemma i p
    D-ar-src-lemma i (D-μ-add x p) = D-ar-src-lemma i p
    D-ar-src-lemma i (D-μ-rmv x p)
      rewrite D-ar-src-lemma i p
        = sym (φ-ar-lemma (suc i) (x ◂ pop (D-src p)) (x , pop (D-src p)) refl)
    D-ar-src-lemma {ty = μ ty} i (D-μ-dwn p refl ho x)
      rewrite D-ar-src-lemma 0 p 
        | ar-std-lemma (suc i) 0 (plugv 0 (D-src p) (vmap (pop ∘ D-src) x))
        = trans (cong (λ P → P + vsum (vmap (D-arᵢ i) x))
                      (trans (D-ar-src-lemma (suc i) p)
                             (cong (ar (suc i))
                                   (sym (fgt-plugv-lemma 0 (D-src p)
                                        (vmap (pop ∘ D-src) x))))))
          (cong (λ P → ar (suc i) (fgt 0 (plugv 0 (D-src p) (vmap (pop ∘ D-src) x))) + P) (sym
            (trans (cong (λ P → sum (map (ar (suc i)) P))
                   (ch-plugv-lemma 0 (D-src p) (vmap (pop ∘ D-src) x)))
            (trans (cong sum (sym (toList-vmap (ar (suc i)) (vmap (pop ∘ D-src) x))))
            (trans (cong (λ P → sum (toList P)) (vmap-compose x))
            (trans (sym (vsum-spec (vmap (ar (suc i) ∘ pop {a = μ ty} ∘ D-src) x)))
                   (cong (λ P → vsum (vmap P x))
                     (fun-ext (λ k → sym (D-ar-src-lemma i k)))))))))) 
\end{code}

\begin{code}
  mutual
\end{code}
%<*D-dst-type>
\begin{code}
    {-# TERMINATING #-}
    D-dst : {n : ℕ}{t : T n}{ty : U n}
          → Patch ty t → ElU ty t
\end{code}
%</D-dst-type>
%<*D-ar-dst-lemma-type>
\begin{code}
    D-ar-dst-lemma
      : {n : ℕ}{t : T n}{ty : U n}
      → (i : ℕ)(p : Patch ty t)
      → D-arₒ i p ≡ ar i (D-dst p)
\end{code}
%</D-ar-dst-lemma-type>
%<*D-dst-def>
\begin{code}
    D-dst (D-A ())
    D-dst D-unit = unit
    D-dst (D-inl d) = inl (D-dst d)
    D-dst (D-inr d) = inr (D-dst d)
    D-dst (D-setl _ x) = inr x
    D-dst (D-setr _ x) = inl x
    D-dst (D-pair d e) = D-dst d , D-dst e
    D-dst (D-def d) = red (D-dst d)
    D-dst (D-top d) = top (D-dst d)
    D-dst (D-pop d) = pop (D-dst d)
    D-dst (D-μ-dwn p hi ho d)
      rewrite D-ar-dst-lemma 0 p
        = mu (plugv 0 (D-dst p) (vmap (pop ∘ D-dst) (vec-reindx (sym ho) d)))
    D-dst (D-μ-rmv ctx d)
      = D-dst d
    D-dst (D-μ-add ctx d)
      = mu (ctx ◂ pop (D-dst d))
\end{code}
%</D-dst-def>
\begin{code}
    D-ar-dst-lemma i (D-A ())
    D-ar-dst-lemma i D-unit = refl
    D-ar-dst-lemma i (D-inl d) = D-ar-dst-lemma i d
    D-ar-dst-lemma i (D-inr d) = D-ar-dst-lemma i d
    D-ar-dst-lemma i (D-setl x x₁) = refl
    D-ar-dst-lemma i (D-setr x x₁) = refl
    D-ar-dst-lemma i (D-pair d d₁)
      = cong₂ _+_ (D-ar-dst-lemma i d) (D-ar-dst-lemma i d₁)
    D-ar-dst-lemma i (D-def d) = D-ar-dst-lemma (suc i) d
    D-ar-dst-lemma zero (D-top d) = refl
    D-ar-dst-lemma (suc i) (D-top d) = D-ar-dst-lemma i d
    D-ar-dst-lemma zero (D-pop d) = refl
    D-ar-dst-lemma (suc i) (D-pop d) = D-ar-dst-lemma i d
    D-ar-dst-lemma i (D-μ-rmv x d) = D-ar-dst-lemma i d
    D-ar-dst-lemma i (D-μ-add x d)
      rewrite D-ar-dst-lemma i d
        = sym (φ-ar-lemma (suc i) (x ◂ pop (D-dst d)) (x , pop (D-dst d)) refl)
    D-ar-dst-lemma {ty = μ ty} i (D-μ-dwn p hi refl x)
      rewrite D-ar-dst-lemma 0 p
        | ar-std-lemma (suc i) 0 (plugv 0 (D-dst p) (vmap (pop ∘ D-dst) x))
        = trans (cong (λ P → P + vsum (vmap (D-arₒ i) x))
                      (trans (D-ar-dst-lemma (suc i) p)
                             (cong (ar (suc i))
                                   (sym (fgt-plugv-lemma 0 (D-dst p)
                                        (vmap (pop ∘ D-dst) x))))))
          (cong (λ P → ar (suc i) (fgt 0 (plugv 0 (D-dst p) (vmap (pop ∘ D-dst) x))) + P) (sym
            (trans (cong (λ P → sum (map (ar (suc i)) P))
                   (ch-plugv-lemma 0 (D-dst p) (vmap (pop ∘ D-dst) x)))
            (trans (cong sum (sym (toList-vmap (ar (suc i)) (vmap (pop ∘ D-dst) x))))
            (trans (cong (λ P → sum (toList P)) (vmap-compose x))
            (trans (sym (vsum-spec (vmap (ar (suc i) ∘ pop {a = μ ty} ∘ D-dst) x)))
                   (cong (λ P → vsum (vmap P x))
                     (fun-ext (λ k → sym (D-ar-dst-lemma i k))))))))))
                  
\end{code}
