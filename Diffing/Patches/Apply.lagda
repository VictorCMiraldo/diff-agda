\begin{code}
{-# OPTIONS --rewriting #-}
open import Prelude
open import Prelude.Vector

open import Diffing.CF-base
open import CF.Derivative
  using (match; _◂_)
open import Diffing.Patches.D

module Diffing.Patches.Apply where
\end{code}

\begin{code}
  {-# REWRITE D-ar-src-lemma #-}
  {-# REWRITE D-ar-dst-lemma #-}
  mutual
\end{code}
\begin{code}
    {-# TERMINATING #-}
    gapply : {n : ℕ}{t : T n}{ty : U n}
           → (p : Patch ty t)(x : ElU ty t)
           → Maybe (ElU ty t)
\end{code}
\begin{code}
    postulate
      gapply-correct
        : {n : ℕ}{t : T n}{ty : U n}
        → (p : Patch ty t)
        → gapply p (D-src p) ≡ just (D-dst p)

      gapply-sound
        : {n : ℕ}{t : T n}{ty : U n}
        → (p : Patch ty t)(x y : ElU ty t)
        → gapply p x ≡ just y
        → D-src p ≡ x × D-dst p ≡ y
\end{code}
\begin{code}
    gapply (D-A ()) x
    gapply D-unit unit = just unit
    gapply (D-inl p) (inl x) = inl <M> gapply p x
    gapply (D-inl p) (inr x) = nothing
    gapply (D-inr p) (inl x) = nothing
    gapply (D-inr p) (inr x) = inr <M> gapply p x
    gapply (D-setl p q) (inl x)
      with p ≟-U x
    ...| no  _ = nothing
    ...| yes _ = just (inr q)
    gapply (D-setl p q) (inr x) = nothing
    gapply (D-setr p q) (inl x) = nothing
    gapply (D-setr p q) (inr x)
      with p ≟-U x
    ...| no  _ = nothing
    ...| yes _ = just (inl q)
    gapply (D-pair p q) (x , y)
      = _,_ <M> gapply p x <M*> gapply q y
    gapply (D-def p) (red x) = red <M> gapply p x
    gapply (D-top p) (top x) = top <M> gapply p x
    gapply (D-pop p) (pop x) = pop <M> gapply p x
    gapply (D-μ-add ctx p) x
      = (mu ∘ _◂_ ctx ∘ pop) <M>  gapply p x
    gapply (D-μ-rmv ctx p) (mu x)
      with match ctx x
    ...| nothing = nothing
    ...| just (pop x') = gapply p x'
    gapply (D-μ-dwn p hi refl q) (mu x)
      with gapply p (fgt 0 x) | inspect (gapply p) (fgt 0 x)
    ...| nothing | _ = nothing
    ...| just x' | [ R ]
       = (mu ∘ plugv 0 x')
         <M> vmapM (λ { (q₀ , pop x₀) → pop <M> gapply q₀ x₀ })
                   (vec-reindx (cong (ar 0) (p2 (gapply-sound p (fgt 0 x) x' R)))
                   (vzip (trans (sym hi)
                                (cong (ar 0) (p1 (gapply-sound p (fgt 0 x) x' R))))
                          q (chv 0 x)))
\end{code}

begin{code}
    gapply-correct (D-A x) = {!!}
    gapply-correct D-unit = {!!}
    gapply-correct (D-inl p) = {!!}
    gapply-correct (D-inr p) = {!!}
    gapply-correct (D-setl x x₁)
      rewrite ≟-U-refl x = refl
    gapply-correct (D-setr x x₁) = {!!}
    gapply-correct (D-pair p p₁) = {!!}
    gapply-correct (D-def p) = {!!}
    gapply-correct (D-top p) = {!!}
    gapply-correct (D-pop p) = {!!}
    gapply-correct (D-μ-dwn p refl ho x)
            = {!!}
    gapply-correct (D-μ-add x p) = {!!}
    gapply-correct (D-μ-rmv x p) = {!!}

    gapply-sound (D-A ()) x₁ y hip
    gapply-sound D-unit x y hip = {!!}
    gapply-sound (D-inl p) x y hip = {!!}
    gapply-sound (D-inr p) x y hip = {!!}
    gapply-sound (D-setl a b) x y hip = {!!}
    gapply-sound (D-setr a b) x y hip = {!!}
    gapply-sound (D-pair p q) x y hip = {!!}
    gapply-sound (D-def p) x y hip = {!!}
    gapply-sound (D-top p) x y hip = {!!}
    gapply-sound (D-pop p) x y hip = {!!}
    gapply-sound (D-μ-dwn p hi refl q) (mu x) y hip
      = {!!}
    gapply-sound (D-μ-add ctx p) x y hip
      with <M>-elim hip
    ...| r , s , t with gapply-sound p x r t
    ...| h0 , h1 = h0 , trans (cong (λ P → mu (ctx ◂ pop P)) h1) (sym s)
    gapply-sound (D-μ-rmv ctx p) x y hip = {!!}
end{code}
