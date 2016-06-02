\begin{code}
open import Prelude
open import Diffing.Universe

open import Diffing.Patches.Diff
open import Diffing.Patches.Diff.Functor using (cast; forget)
open import Diffing.Patches.Diff.Id
open import Diffing.Patches.Diff.Alignment
open import Diffing.Patches.Conflicts

module Diffing.Patches.Residual where
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
      = D-inl (res p q (||-inl-elim {p = p} {q = q} hip))
    res (D-inl p) (D-setl xa xb) hip
      with Is-diff-id? p
    ...| yes _ = D-setl xa xb
    ...| no  _ = D-A (UpdUpd (inl xa) {!!} (inr xb))
    res (D-setl xa xb) (D-inl q) hip
      with Is-diff-id? q
    ...| yes _ = D-setl xa xb
    ...| no  _ = D-A (UpdUpd (inl xa) (inr xb) {!!})
    res (D-setl xa xb) (D-setl xc xd) hip
      with xb ≟-U xd
    ...| no  _ = D-A (UpdUpd (inl xa) (inr xb) (inr xd))
    ...| yes _ = cast (gdiff-id (inr xb))

    res (D-inr p) (D-inr q) hip
      = D-inr (res p q (||-inr-elim {p = p} {q} hip))
    res (D-inr p) (D-setr xa xb) hip
      with Is-diff-id? p
    ...| yes _ = D-setr xa xb
    ...| no  _ = D-A (UpdUpd (inr xa) {!!} (inl xb)) 
    res (D-setr xa xb) (D-inr q) hip
      with Is-diff-id? q
    ...| yes _ = D-setr xa xb
    ...| no  _ = D-A (UpdUpd (inr xa) (inl xb) {!!}) 
    res (D-setr xa xb) (D-setr xc xd) hip
      with xb ≟-U xd
    ...| no  _ = D-A (UpdUpd (inr xa) (inl xb) (inl xd))
    ...| yes _ = cast (gdiff-id (inl xb)) 
    
    res (D-inl p) (D-inr q)     hip
      = ⊥-elim (||-inl-inr-⊥ {p = p} {q = q} hip)
    res (D-inl p) (D-setr x x₁) hip
      = ⊥-elim (||-inl-setr-⊥ {p = p} {x = x₁} {y = x} hip)
    res (D-inr p) (D-inl q) hip
      = ⊥-elim (||-inl-inr-⊥ {p = q} {q = p}
               (||-sym {p = D-inr p} {D-inl q} hip))
    res (D-inr p) (D-setl x x₁) hip
      = ⊥-elim (||-inr-setl-⊥ {p = p} {x = x} {y = x₁} hip)
    res (D-setl xa xb) (D-inr q) hip
      = ⊥-elim (||-inr-setl-⊥ {p = q} {x = xa} {y = xb}
               (||-sym {p = D-setl xa xb} {D-inr q} hip))
    res (D-setl xa xb) (D-setr xc xd) hip
      = ⊥-elim (||-setl-setr-⊥ {A = ⊥ₚ} {x = xa} {xd} {xb} {xc} hip)
    res (D-setr xa xb) (D-inl q) hip
      = ⊥-elim (||-inl-setr-⊥ {p = q} {x = xb} {y = xa}
                (||-sym {p = D-setr xa xb} {q = D-inl q} hip))
    res (D-setr xa xb) (D-setl xc xd) hip
      = ⊥-elim (||-setl-setr-⊥ {A = ⊥ₚ} {x = xc} {xb} {xd} {xa}
                (||-sym {A = ⊥ₚ} {p = D-setr xa xb} {q = D-setl xc xd} hip))
    
    res (D-pair d1 d2) (D-pair e1 e2) hip
      = let hip1 , hip2 = ||-pair-elim {q1 = d1} {e1} {d2} {e2} hip
         in D-pair (res d1 e1 hip1) (res d2 e2 hip2)

    res (D-def p) (D-def q) hip
      = D-def (res p q (||-def-elim {p = p} {q} hip))
    res (D-top p) (D-top q) hip
      = D-top (res p q (||-top-elim {p = p} {q} hip))
    res (D-pop p) (D-pop q) hip
      = D-pop (res p q (||-pop-elim {p = p} {q} hip))
         
    res (D-mu x) (D-mu y) hip
      = D-mu (resμ x y (||-mu-elim {p = x} {y} hip))    

    resμ : {n : ℕ}{t : T n}{ty : U (suc n)}
         → (ps qs : Patchμ t ty) → ps ||μ qs → List (Dμ C t ty)
    resμ [] [] hip = []
    resμ  _ (Dμ-A () ∷ _) _
    resμ  (Dμ-A () ∷ _) _ _

    resμ (Dμ-ins a ∷ ps) (Dμ-ins b ∷ qs) hip
      with a ≟-U b
    ...| yes _ = resμ ps qs hip
    ...| no  _ = Dμ-A (GrowLR a b) ∷ resμ ps qs hip
    resμ (Dμ-ins a ∷ ps) qs hip
      = Dμ-A (GrowL a) ∷ resμ ps qs hip
    resμ ps (Dμ-ins b ∷ qs) hip
      = Dμ-A (GrowR b) ∷ resμ ps qs hip

    resμ (Dμ-dwn x ∷ ps) (Dμ-dwn y ∷ qs) hip
      = let ps||qs , x||y = ||μ-dwn-dwn-elim {x = x} {y} {ps} {qs} hip
         in Dμ-dwn (res x y x||y) ∷ resμ ps qs ps||qs

    resμ (Dμ-dwn x ∷ ps) (Dμ-del y ∷ qs) hip
      with Is-diff-id? x
    ...| no  _ = Dμ-A (UpdDel {!!} y)
               ∷ resμ ps qs (||μ-dwn-del-elim {a = y} {x = x} {ps} {qs} hip)
    ...| yes _ = resμ ps qs (||μ-dwn-del-elim {a = y} {x = x} {ps} {qs} hip)

    resμ (Dμ-del x ∷ ps) (Dμ-del y ∷ qs) hip
      = {!!}

    resμ (Dμ-del x ∷ ps) (Dμ-dwn y ∷ qs) hip
      with Is-diff-id? y
    ...| no  _ = Dμ-A (DelUpd x {!!})
               ∷ resμ ps qs (||μ-sym {p = qs} {ps} (||μ-dwn-del-elim {a = x} {x = y} {qs} {ps}
                            (||μ-sym {p = Dμ-del x ∷ ps} {Dμ-dwn y ∷ qs} hip)))
    ...| yes _ = Dμ-del x
               ∷ resμ ps qs (||μ-sym {p = qs} {ps} (||μ-dwn-del-elim {a = x} {x = y} {qs} {ps}
                            (||μ-sym {p = Dμ-del x ∷ ps} {Dμ-dwn y ∷ qs} hip)))
    
    
    resμ [] (x ∷ qs) hip = {!!}
    resμ (x ∷ ps) [] hip = {!!}
\end{code}

