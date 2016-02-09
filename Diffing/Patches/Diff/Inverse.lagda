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
    D-inv : {n : ℕ}{t : Tel n}{ty : U n}
          → Patch t ty → Patch t ty
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
    D-inv-cost : {n : ℕ}{t : Tel n}{ty : U n}
               → (d : Patch t ty)
               → cost d ≡ cost (D-inv d)
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
    D-inv-sound 
      : {n : ℕ}{t : Tel n}{ty : U n}
      → (a b : ElU ty t)
      → gapply (D-inv (gdiff a b)) b ≡ just a
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

begin{code}
  inv-bias : {n : ℕ}{t : Tel n}{ty : U (suc n)}
           → (p q : Patchμ t ty) 
           → bias p q 
           → bias (Dμ-inv p) (Dμ-inv q)
  inv-bias [] [] ()
  inv-bias [] (q ∷ qs) hip = unit
  inv-bias (p ∷ ps) [] ()
  inv-bias (p ∷ ps) (q ∷ qs) (i1 x) 
    = i1 (subst (λ P → suc P ≤ costμ (Dμ-inv1 q)) (Dμ-inv-cost p) 
         (subst (λ P → suc (costμ p) ≤ P) (Dμ-inv-cost q) x))
  inv-bias (p ∷ ps) (q ∷ qs) (i2 (c≡ , rec)) 
    = i2 (trans (sym (Dμ-inv-cost p)) (trans c≡ (Dμ-inv-cost q)) 
         , inv-bias ps qs rec)

end{code}
  ⊔μ-cross : {n : ℕ}{t : Tel n}{ty : U (suc n)}
           → (d1 d2 d3 : Patchμ t ty)
           → d1 ⊔μ (d2 ⊔μ d3) ≡ d2 ⊔μ (d1 ⊔μ d3)
  ⊔μ-cross d1 d2 d3 
    = trans (⊔μ-assoc d1 d2 d3) 
      (trans (cong (λ P → P ⊔μ d3) (⊔μ-comm d1 d2)) 
       (sym (⊔μ-assoc d2 d1 d3)))

  private
    fix : {n : ℕ}{t : Tel n}{ty : U (suc n)}
        → (d1 d2 : Patchμ t ty)
        → suc (costL (Dμ-inv d1)) ≤ costL (Dμ-inv d2)
        → suc (costL d1) ≤ costL d2
    fix d1 d2 p = {!!}

  ⊔μ-inv-lemma : {n : ℕ}{t : Tel n}{ty : U (suc n)}
               → (d1 d2 : Patchμ t ty)
               → Dμ-inv (d1 ⊔μ d2) ≡ Dμ-inv d1 ⊔μ Dμ-inv d2
  ⊔μ-inv-lemma d1 d2 with comp (costL (Dμ-inv d1)) (costL (Dμ-inv d2))
  ⊔μ-inv-lemma d1 d2 | LE x 
    rewrite comp-NEQ {q = nat-≤-abs (fix d1 d2 x)} (fix d1 d2 x) 
          | comp-GE x
         = {!!}
  ⊔μ-inv-lemma d1 d2 | GE x = {!!}
  ⊔μ-inv-lemma d1 d2 | EQ x = {!!}

  ⊔μ-inv-lemma-3 : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                 → (d1 d2 d3 : Patchμ t ty)
                 → Dμ-inv (d1 ⊔μ (d2 ⊔μ d3)) 
                 ≡ Dμ-inv d1 ⊔μ (Dμ-inv d2 ⊔μ Dμ-inv d3)
  ⊔μ-inv-lemma-3 d1 d2 d3 = {!!}

  mutual
    {-# TERMINATING #-}
    D-inv-sound 
      : {n : ℕ}{t : Tel n}{ty : U n}
      → (a b : ElU ty t)
      → D-inv (gdiff a b) ≡ gdiff b a
    D-inv-sound void void = refl
    D-inv-sound (inl p) (inl q) = cong D-inl (D-inv-sound p q)
    D-inv-sound (inl p) (inr q) = refl
    D-inv-sound (inr p) (inl q) = refl
    D-inv-sound (inr p) (inr q) = cong D-inr (D-inv-sound p q)
    D-inv-sound (p1 , p2) (q1 , q2) 
      = cong₂ D-pair (D-inv-sound p1 q1) (D-inv-sound p2 q2)
    D-inv-sound (top p) (top q) 
      = cong D-top (D-inv-sound p q)
    D-inv-sound (pop p) (pop q) = cong D-pop (D-inv-sound p q)
    D-inv-sound (mu p) (mu q) = cong D-mu (Dμ-inv-sound (mu p ∷ []) (mu q ∷ []))
    D-inv-sound (red p) (red q) = cong D-β (D-inv-sound p q)


    Dμ-inv-sound
      : {n : ℕ}{t : Tel n}{ty : U (suc n)}
      → (as bs : List (ElU (μ ty) t))
      → Dμ-inv (gdiffL as bs) ≡ gdiffL bs as
    Dμ-inv-sound [] [] = refl
    Dμ-inv-sound [] (b ∷ bs)
      = cong₂ _∷_ refl (Dμ-inv-sound [] (μ-ch b ++ bs))
    Dμ-inv-sound (a ∷ as) [] 
      = cong₂ _∷_ refl (Dμ-inv-sound (μ-ch a ++ as) [])
    Dμ-inv-sound (a ∷ as) (b ∷ bs)
      = let
        a1 = Dμ-ins (μ-hd b)
        a2 = Dμ-del (μ-hd a)
        a3 = Dμ-dwn (gdiff (μ-hd a) (μ-hd b))
        d1 = gdiffL (a ∷ as) (μ-ch b ++ bs)
        d2 = gdiffL (μ-ch a ++ as) (b ∷ bs)
        d3 = gdiffL (μ-ch a ++ as) (μ-ch b ++ bs)
        b1 = Dμ-ins (μ-hd a)
        b2 = Dμ-del (μ-hd b)
        b3 = Dμ-dwn (gdiff (μ-hd b) (μ-hd a))
        e1 = gdiffL (b ∷ bs) (μ-ch a ++ as) 
        e2 = gdiffL (μ-ch b ++ bs) (a ∷ as)
        e3 = gdiffL (μ-ch b ++ bs) (μ-ch a ++ as)
      in begin
           Dμ-inv
            ((a1 ∷ d1) ⊔μ (a2 ∷ d2) ⊔μ (a3 ∷ d3))
         ≡⟨ ⊔μ-inv-lemma-3 (a1 ∷ d1) (a2 ∷ d2) (a3 ∷ d3) ⟩
           Dμ-inv (a1 ∷ d1) ⊔μ Dμ-inv (a2 ∷ d2) ⊔μ Dμ-inv (a3 ∷ d3) 
         ≡⟨ cong (λ P → P ⊔μ Dμ-inv (a2 ∷ d2) ⊔μ Dμ-inv (a3 ∷ d3)) {x = Dμ-inv (a1 ∷ d1)}
              (cong₂ _∷_ refl (Dμ-inv-sound (a ∷ as) (μ-ch b ++ bs))) ⟩
           (b2 ∷ e2) ⊔μ Dμ-inv (a2 ∷ d2) ⊔μ Dμ-inv (a3 ∷ d3)
         ≡⟨ cong (λ P → (b2 ∷ e2) ⊔μ P ⊔μ Dμ-inv (a3 ∷ d3)) {x = Dμ-inv (a2 ∷ d2)}
              (cong₂ _∷_ refl (Dμ-inv-sound (μ-ch a ++ as) (b ∷ bs))) ⟩
           (b2 ∷ e2) ⊔μ (b1 ∷ e1) ⊔μ Dμ-inv (a3 ∷ d3)
         ≡⟨ cong (λ P → (b2 ∷ e2) ⊔μ (b1 ∷ e1) ⊔μ P) 
              (cong₂ _∷_ (cong Dμ-dwn (D-inv-sound (μ-hd a) (μ-hd b))) 
                         (Dμ-inv-sound (μ-ch a ++ as) (μ-ch b ++ bs))) ⟩
           (b2 ∷ e2) ⊔μ (b1 ∷ e1) ⊔μ (b3 ∷ e3)
         ≡⟨ ⊔μ-cross (b2 ∷ e2) (b1 ∷ e1) (b3 ∷ e3) ⟩
           (b1 ∷ e1) ⊔μ (b2 ∷ e2) ⊔μ (b3 ∷ e3)
           ∎
      where
        open import Relation.Binary.PropositionalEquality as PropEq
        open PropEq.≡-Reasoning
\end{code}
