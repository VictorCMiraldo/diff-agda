\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.MuUtils
open import Diffing.Universe.Equality
open import Diffing.Universe.Measures
open import Diffing.Patches.Diff

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

    Dμ-inv : {n : ℕ}{t : Tel n}{ty : U (suc n)}
           → Patchμ t ty → Patchμ t ty
    Dμ-inv [] = []
    Dμ-inv (Dμ-A () ∷ ps)
    Dμ-inv (Dμ-ins x ∷ ps) = Dμ-del x ∷ Dμ-inv ps
    Dμ-inv (Dμ-del x ∷ ps) = Dμ-ins x ∷ Dμ-inv ps
    Dμ-inv (Dμ-cpy x ∷ ps) = Dμ-cpy x ∷ Dμ-inv ps
    Dμ-inv (Dμ-dwn dx ∷ ps) = Dμ-dwn (D-inv dx) ∷ Dμ-inv ps
\end{code}

\begin{code}
  mutual
    D-inv-cost : {n : ℕ}{t : Tel n}{ty : U n}
               → (d : Patch t ty)
               → cost d ≡ cost (D-inv d)
    D-inv-cost (D-A ())
    D-inv-cost D-void = refl
    D-inv-cost (D-inl d) = cong suc (D-inv-cost d)
    D-inv-cost (D-inr d) = cong suc (D-inv-cost d)
    D-inv-cost (D-setl x x₁) = cong₂ _+_ (+-comm (sizeElU x) (sizeElU x₁)) 
                               (cong (λ P → P + zero) (+-comm (sizeElU x) (sizeElU x₁)))
    D-inv-cost (D-setr x x₁) = cong₂ _+_ (+-comm (sizeElU x) (sizeElU x₁)) 
                               (cong (λ P → P + zero) (+-comm (sizeElU x) (sizeElU x₁)))
    D-inv-cost (D-pair p q) = cong₂ _+_ (D-inv-cost p) (D-inv-cost q)
    D-inv-cost (D-mu x) = Dμ-inv-cost x
    D-inv-cost (D-β d) = D-inv-cost d
    D-inv-cost (D-top d) = D-inv-cost d
    D-inv-cost (D-pop d) = D-inv-cost d

    Dμ-inv-cost : {n : ℕ}{t : Tel n}{ty : U (suc n)}
               → (d : Patchμ t ty)
               → cost (D-mu d) ≡ cost (D-mu (Dμ-inv d))
    Dμ-inv-cost [] = refl
    Dμ-inv-cost (Dμ-A () ∷ d)
    Dμ-inv-cost (Dμ-ins x ∷ d) = cong (λ P → sizeElU x + 1 + P) (Dμ-inv-cost d)
    Dμ-inv-cost (Dμ-del x ∷ d) = cong (λ P → sizeElU x + 1 + P) (Dμ-inv-cost d)
    Dμ-inv-cost (Dμ-cpy x ∷ d) = Dμ-inv-cost d
    Dμ-inv-cost (Dμ-dwn x ∷ d) = cong₂ _+_ (D-inv-cost x) (Dμ-inv-cost d)
\end{code}

\begin{code}
  postulate 
    ⊔μ-cross : {n : ℕ}{t : Tel n}{ty : U (suc n)}
             → (d1 d2 d3 : Patchμ t ty)
             → d1 ⊔μ (d2 ⊔μ d3) ≡ d2 ⊔μ (d1 ⊔μ d3)

  mutual
    {-# TERMINATING #-}
    D-inv-sound 
      : {n : ℕ}{t : Tel n}{ty : U n}
      → (a b : ElU ty t)
      → D-inv (gdiff a b) ≡-D gdiff b a
    D-inv-sound void void x = refl
    D-inv-sound (inl a) (inl b) (inl x) = cong (_<M>_ inl) (D-inv-sound a b x)
    D-inv-sound (inl a) (inl b) (inr x) = refl
    D-inv-sound (inl a) (inr b) (inl x) = refl
    D-inv-sound (inl a) (inr b) (inr x) = {!!}
    D-inv-sound (inr a) (inl b) (inl x) = {!!}
    D-inv-sound (inr a) (inl b) (inr x) = refl
    D-inv-sound (inr a) (inr b) (inl x) = refl
    D-inv-sound (inr a) (inr b) (inr x) = {!!}
    D-inv-sound (a₁ , a₂) (b₁ , b₂) (x₁ , x₂) = {!!}
    D-inv-sound (top a) (top b) (top x) = {!!}
    D-inv-sound (pop a) (pop b) (pop x) = {!!}
    D-inv-sound (mu a) (mu b) (mu x) = cong (λ P → P >>= safeHead)
                                         (Dμ-inv-sound (mu a ∷ []) (mu b ∷ []) (mu x ∷ []))
    D-inv-sound (red a) (red b) (red x) = {!!}

    Dμ-inv-sound
      : {n : ℕ}{t : Tel n}{ty : U (suc n)}
      → (as bs : List (ElU (μ ty) t))
      → Dμ-inv (gdiffL as bs) ≡-Dμ gdiffL bs as
    Dμ-inv-sound [] [] [] = refl
    Dμ-inv-sound [] [] (x ∷ xs) = refl
    Dμ-inv-sound [] (b ∷ bs) [] = refl
    Dμ-inv-sound [] (b ∷ bs) (x ∷ xs) 
      with μ-open x
    ...| hdX , chX with μ-hd b ≟-U hdX
    ...| no  _ = refl
    ...| yes _ = Dμ-inv-sound [] (μ-ch b ++ bs) (chX ++ xs)
    Dμ-inv-sound (a ∷ as) [] [] = cong (λ P → P >>= (gIns (μ-hd a))) (Dμ-inv-sound (μ-ch a ++ as) [] [])
    Dμ-inv-sound (a ∷ as) [] (x ∷ xs) = {!cong!}
    Dμ-inv-sound (a ∷ as) (b ∷ bs) [] = {!!}
    Dμ-inv-sound (a ∷ as) (b ∷ bs) (x ∷ xs)
      with μ-open a | μ-open b
    ...| hdA , chA | hdB , chB with hdA ≟-U hdB
    ...| yes p rewrite sym p | ≟-U-refl hdA
       = cong (λ P → _>>=_ (_>>=_ (gDel hdA (x ∷ xs)) P) (gIns hdA)) 
         (congPμ gapplyL 
           {d1 = Dμ-inv (gdiffL (chA ++ as) (chB ++ bs))} 
           {d2 = gdiffL (chB ++ bs) (chA ++ as)} 
           (Dμ-inv-sound (chA ++ as) (chB ++ bs)))
    ...| no ¬p with hdB ≟-U hdA
    ...| yes q = ⊥-elim (¬p (sym q))
    ...| no  _ 
       rewrite sym (⊔μ-cross (Dμ-ins hdA ∷ gdiffL (b ∷ bs) (chA ++ as)) 
                         (Dμ-del hdB ∷ gdiffL (chB ++ bs) (a ∷ as)) 
                         (Dμ-dwn (gdiff (red hdB) (red hdA)) ∷ gdiffL bs as))
             = {! congPμ (λ P → gapplyL P (x ∷ xs)) 
               (⊔μ-≡ (Dμ-ins hdB ∷ gdiffL (a ∷ as) (chB ++ bs))
                     ((Dμ-del hdA ∷ gdiffL (chA ++ as) (b ∷ bs)) ⊔μ
                             (Dμ-dwn (gdiff (red hdB) (red hdA)) ∷ gdiffL as bs)) 
                     {!!} 
                     (⊔μ-≡ (Dμ-del hdA ∷ gdiffL (chA ++ as) (b ∷ bs))
                           (Dμ-dwn (gdiff (red hdB) (red hdA)) ∷ gdiffL as bs) 
                           {!!} 
                           {!!})) !}
\end{code}
