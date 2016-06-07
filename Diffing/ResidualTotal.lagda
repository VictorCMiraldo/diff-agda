\begin{code}
open import Prelude
open import Diffing.Universe

open import Diffing.Patches.D
open import Diffing.Patches.Functor using (cast; forget)
open import Diffing.Patches.Id
open import Diffing.Patches.Properties.WellFounded
open import Diffing.Patches.Properties.Alignment
open import Diffing.Conflicts.C

module Diffing.ResidualTotal where
\end{code}

  Residuals are the heart of a merge. the patch (p / q),
  if defined, is the patch that incorporates the changes
  that p did, but on an object already altered by q.

  The simplified (informal) diagram is:

                    A₁
                p ↙    ↘ q
                A₂      A₃
            (q/p) ↘    ↙ (p/q) 
                    A₄

  It only makes sense to calculate the residual of aligned patches,
  meaning that they must be defined for the same inputs.

  Here we use some sort of trick to comply with that notion.
  We define alignment on top of _/_. That is,
  we say that two patches p and q are aligned iff (p/q) is just x, for some x.

  If (dx / dy) ≡ nothing, it means that dx and dy are NOT aligned.

  If (dx / dy) ≡ just k, it means that dx and dy are aligned and
                         a merge is given by k. 

  Note that upon having (dx / dy) ≡ just k, it is not always the case
  that they merge peacefully. k might contain conflicts inside!

\begin{code}
  mutual
    {-# TERMINATING #-}
\end{code}
%<*residual-type>
\begin{code}
    res : {n : ℕ}{t : T n}{ty : U n}
        → (p q : Patch t ty)(hip : p || q)
        → D C t ty
\end{code}
%</residual-type>
\begin{code}
    res (D-A ()) q hip
    res p (D-A ()) hip
    res D-unit D-unit hip = D-unit
    
    res {ty = ty ⊕ tv} (D-inl p) (D-inl q) hip
      = D-inl (res p q (||-inl-elim p q hip))
    res (D-inl p) (D-setl xa xb) hip
      with Is-diff-id? p
    ...| yes _ = D-setl xa xb
    ...| no  _ = D-A (UpdUpd (inl xa) (D-dst-wf ((D-inl p) , p1 (||-elim hip))) (inr xb))
    res (D-setl xa xb) (D-inl q) hip
      with Is-diff-id? q
    ...| yes _ = D-setl xa xb
    ...| no  _ = D-A (UpdUpd (inl xa) (inr xb) (D-dst-wf (D-inl q , p1 (p2 (||-elim hip)))))
    res (D-setl xa xb) (D-setl xc xd) hip
      with xb ≟-U xd
    ...| no  _ = D-A (UpdUpd (inl xa) (inr xb) (inr xd))
    ...| yes _ = cast (gdiff-id (inr xb))

    res (D-inr p) (D-inr q) hip
      = D-inr (res p q (||-inr-elim p q hip))
    res (D-inr p) (D-setr xa xb) hip
      with Is-diff-id? p
    ...| yes _ = D-setr xa xb
    ...| no  _ = D-A (UpdUpd (inr xa) (D-dst-wf (D-inr p , p1 (||-elim hip))) (inl xb)) 
    res (D-setr xa xb) (D-inr q) hip
      with Is-diff-id? q
    ...| yes _ = D-setr xa xb
    ...| no  _ = D-A (UpdUpd (inr xa) (inl xb) (D-dst-wf (D-inr q , p1 (p2 (||-elim hip))))) 
    res (D-setr xa xb) (D-setr xc xd) hip
      with xb ≟-U xd
    ...| no  _ = D-A (UpdUpd (inr xa) (inl xb) (inl xd))
    ...| yes _ = cast (gdiff-id (inl xb)) 
    
    res (D-inl p) (D-inr q) hip
      = ⊥-elim (||-inl-inr-⊥ p q hip)
    res (D-inl p) (D-setr x x₁) hip
      = ⊥-elim (||-inl-setr-⊥ p x₁ x hip)
    res (D-inr p) (D-inl q) hip
      = ⊥-elim (||-inl-inr-⊥ q p (||-sym hip))
    res (D-inr p) (D-setl x x₁) hip
      = ⊥-elim (||-inr-setl-⊥ p x x₁ hip)
    res (D-setl xa xb) (D-inr q) hip
      = ⊥-elim (||-inr-setl-⊥ q xa xb (||-sym hip))
    res (D-setl xa xb) (D-setr xc xd) hip
      = ⊥-elim (||-setl-setr-⊥ xa xd xb xc hip)
    res (D-setr xa xb) (D-inl q) hip
      = ⊥-elim (||-inl-setr-⊥ q xb xa (||-sym hip))
    res (D-setr xa xb) (D-setl xc xd) hip
      = ⊥-elim (||-setl-setr-⊥ xc xb xd xa (||-sym hip))
    
    res (D-pair d1 d2) (D-pair e1 e2) hip
      = let d1e1 , d2e2 = ||-pair-elim d1 e1 d2 e2 hip
         in D-pair (res d1 e1 d1e1) (res d2 e2 d2e2)

    res (D-def p) (D-def q) hip
      = D-def (res p q (||-def-elim p q hip))
    res (D-top p) (D-top q) hip
      = D-top (res p q (||-top-elim p q hip))
    res (D-pop p) (D-pop q) hip
      = D-pop (res p q (||-pop-elim p q hip))
         
    res (D-mu x) (D-mu y) hip
      = D-mu (resμ x y (||-mu-elim x y hip))    

    resμ : {n : ℕ}{t : T n}{ty : U (suc n)}
         → (ps qs : Patchμ t ty) → ps ||μ qs
         → List (Dμ C t ty)
    resμ [] [] hip = []
    resμ  _ (Dμ-A () ∷ _) _
    resμ  (Dμ-A () ∷ _) _ _

    resμ (Dμ-ins a ∷ ps) (Dμ-ins b ∷ qs) hip
      with a ≟-U b
    ...| yes _ = resμ ps qs (||μ-ins-ins-elim a b ps qs hip)
    ...| no  _ = Dμ-A (GrowLR a b) ∷ resμ ps qs (||μ-ins-ins-elim a b ps qs hip)
    resμ (Dμ-ins a ∷ ps) qs hip
      = Dμ-A (GrowL a) ∷ resμ ps qs (||μ-ins-elim a ps qs hip)
    resμ ps (Dμ-ins b ∷ qs) hip
      = Dμ-A (GrowR b) ∷ resμ ps qs (||μ-sym (||μ-ins-elim b qs ps (||μ-sym hip)))

    resμ (Dμ-dwn x ∷ ps) (Dμ-dwn y ∷ qs) hip
      = let psqs , xy = ||μ-dwn-dwn-elim x y ps qs hip
         in Dμ-dwn (res x y xy) ∷ resμ ps qs psqs

    resμ (Dμ-dwn x ∷ ps) (Dμ-del y ∷ qs) hip
      with Is-diff-id? x
    ...| no  _ = Dμ-A (UpdDel (D-dst-wf (x , p1 (Dμ-dwn-wf x ps (p1 (||μ-elim hip))))) y)
               ∷ resμ ps qs (||μ-dwn-del-elim y x ps qs hip)
    ...| yes _ = resμ ps qs (||μ-dwn-del-elim y x ps qs hip)

    resμ (Dμ-del x ∷ ps) (Dμ-del y ∷ qs) hip
      = let psqs , x≡y = ||μ-del-del-elim y x ps qs hip
         in resμ ps qs psqs

    resμ (Dμ-del x ∷ ps) (Dμ-dwn y ∷ qs) hip
      with Is-diff-id? y
    ...| no  _ = Dμ-A (DelUpd x (D-dst-wf (y , p1 (Dμ-dwn-wf y qs (p1 (p2 (||μ-elim hip)))))))
               ∷ resμ ps qs (||μ-sym (||μ-dwn-del-elim x y qs ps (||μ-sym hip)))
    ...| yes _ = Dμ-del x
               ∷ resμ ps qs (||μ-sym (||μ-dwn-del-elim x y qs ps (||μ-sym hip)))
    
    
    resμ [] (x ∷ qs) hip = {!!}
    resμ (x ∷ ps) [] hip = {!!}
\end{code}
