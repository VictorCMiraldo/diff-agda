\begin{code}
open import Prelude
open import Diffing.Universe

open import Diffing.Patches.D
open import Diffing.Patches.Functor using (cast; forget)
open import Diffing.Patches.Id
open import Diffing.Patches.Properties.WellFormed
open import Diffing.Patches.Properties.Alignment
open import Diffing.Conflicts.C

module Diffing.Residual where
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
%<*residual-def>
\begin{code}
    res (D-A ()) q hip
    res p (D-A ()) hip
    res D-unit D-unit hip = D-unit
    
    res {ty = ty ⊕ tv} (D-inl p) (D-inl q) hip
      = D-inl (res p q (||-inl-elim p q hip))
    res (D-inl p) (D-setl xa xb) hip
      with Is-diff-id? p
    ...| yes _  = D-setl xa xb
    ...| no  _  = D-A (UpdUpd  (inl xa) 
                               (D-dst-wf ((D-inl p) , ||-wf-p1 hip)) 
                               (inr xb))
    res (D-setl xa xb) (D-inl q) hip
      with Is-diff-id? q
    ...| yes _  = D-setl xa xb
    ...| no  _  = D-A (UpdUpd  (inl xa) 
                               (inr xb) 
                               (D-dst-wf (D-inl q , ||-wf-p2 hip)))
    res (D-setl xa xb) (D-setl xc xd) hip
      with xb ≟-U xd
    ...| no  _  = D-A (UpdUpd  (inl xa) 
                               (inr xb) 
                               (inr xd))
    ...| yes _  = cast (gdiff-id (inr xb))

    res (D-inr p) (D-inr q) hip
      = D-inr (res p q (||-inr-elim p q hip))
    res (D-inr p) (D-setr xa xb) hip
      with Is-diff-id? p
    ...| yes _  = D-setr xa xb
    ...| no  _  = D-A (UpdUpd  (inr xa) 
                               (D-dst-wf (D-inr p , ||-wf-p1 hip)) 
                               (inl xb)) 
    res (D-setr xa xb) (D-inr q) hip
      with Is-diff-id? q
    ...| yes _  = D-setr xa xb
    ...| no  _  = D-A (UpdUpd  (inr xa) 
                               (inl xb) 
                               (D-dst-wf (D-inr q , ||-wf-p2 hip))) 
    res (D-setr xa xb) (D-setr xc xd) hip
      with xb ≟-U xd
    ...| no  _  = D-A (UpdUpd (inr xa) (inl xb) (inl xd))
    ...| yes _  = cast (gdiff-id (inl xb))
 
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
\end{code}
%</residual-def>
\begin{code}
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
\end{code}
\begin{code}
    resμ : {n : ℕ}{t : T n}{ty : U (suc n)}
         → (ps qs : Patchμ t ty) → ps ||μ qs
         → List (Dμ C t ty)
    resμ [] [] hip = []
    resμ  _ (Dμ-A () ∷ _) _
    resμ  (Dμ-A () ∷ _) _ _
\end{code}
%<*residual-mu-def>
\begin{code}
    resμ (Dμ-ins a ∷ ps) (Dμ-ins b ∷ qs) hip
      with a ≟-U b
    ...| yes _  = resμ ps qs (||μ-ins-ins-elim a b ps qs hip)
    ...| no  _  = Dμ-A (GrowLR a b) 
                ∷ resμ ps qs (||μ-ins-ins-elim a b ps qs hip)

    resμ (Dμ-ins a ∷ ps) qs hip
      = Dμ-A (GrowL a) 
      ∷ resμ ps qs (||μ-ins-elim a ps qs hip)
    resμ ps (Dμ-ins b ∷ qs) hip
      = Dμ-A (GrowR b) 
      ∷ resμ ps qs (||μ-sym (||μ-ins-elim b qs ps (||μ-sym hip)))

    resμ (Dμ-dwn x ∷ ps) (Dμ-dwn y ∷ qs) hip
      = let psqs , xy = ||μ-dwn-dwn-elim x y ps qs hip
         in Dμ-dwn (res x y xy) ∷ resμ ps qs psqs

    resμ (Dμ-dwn x ∷ ps) (Dμ-del y ∷ qs) hip
      with Is-diff-id? x
    ...| no  _ = Dμ-A (UpdDel x y (p1 (Dμ-dwn-wf x ps (||μ-wf-p1 hip))))
               ∷ resμ ps qs (||μ-dwn-del-elim y x ps qs hip)
    ...| yes _ = resμ ps qs (||μ-dwn-del-elim y x ps qs hip)

    resμ (Dμ-del x ∷ ps) (Dμ-del y ∷ qs) hip
      = let psqs , x≡y = ||μ-del-del-elim y x ps qs hip
         in resμ ps qs psqs

    resμ (Dμ-del x ∷ ps) (Dμ-dwn y ∷ qs) hip
      with Is-diff-id? y
    ...| no  _ = Dμ-A (DelUpd x y (p1 (Dμ-dwn-wf y qs (||μ-wf-p2 hip))))
               ∷ resμ ps qs (||μ-sym (||μ-dwn-del-elim x y qs ps (||μ-sym hip)))
    ...| yes _ = Dμ-del x
               ∷ resμ ps qs (||μ-sym (||μ-dwn-del-elim x y qs ps (||μ-sym hip)))
\end{code}
%</residual-mu-def>
\begin{code}
    resμ [] (Dμ-del x ∷ qs) hip
      = ⊥-elim (||μ-[]-del-⊥ x qs hip)
    resμ [] (Dμ-dwn x ∷ qs) hip
      = ⊥-elim (||μ-[]-dwn-⊥ x qs hip)
    resμ (Dμ-del x ∷ ps) [] hip
      = ⊥-elim (||μ-[]-del-⊥ x ps (||μ-sym hip))
    resμ (Dμ-dwn x ∷ ps) [] hip
      = ⊥-elim (||μ-[]-dwn-⊥ x ps (||μ-sym hip))
\end{code}

  Residuals and patch commutation are remarkably similar.
  In fact, we can always "mirror" the result of a residual
  in order to obtain the other residual.

  Proof of this fact in Diffing.Residual.Symmetry

\begin{code}
  on-tail : ∀{a}{A : Set a} → (List A → List A) → List A → List A
  on-tail f [] = []
  on-tail f (x ∷ xs) = x ∷ f xs

  hd-tail : ∀{a}{A : Set a} → (A → A) → (List A → List A) → List A → List A
  hd-tail f tl [] = []
  hd-tail f tl (x ∷ xs) = f x ∷ tl xs

  tail : ∀{a}{A : Set a} → List A → List A
  tail []       = []
  tail (_ ∷ xs) = xs
\end{code}

\begin{code}
  mutual
    mirror : {A B : TU→Set}{n : ℕ}{t : T n}{ty : U n}
           → (p q : D A t ty) → D B t ty → D B t ty

    mirrorμ
      : {A B : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (p q : List (Dμ A t ty)) → List (Dμ B t ty) → List (Dμ B t ty)

    mirror (D-A x) _ r = r
    mirror _ (D-A x) r = r
    
    mirror D-unit D-unit r = r
    
    mirror (D-inl p) (D-inl q) (D-inl r)
      = D-inl (mirror p q r)
    mirror (D-inl p) (D-inl q) r
      = r
    mirror (D-inl p) (D-setl x x₁) r
      = r
    mirror (D-setl x x₁) (D-inl q) r
      = r
    mirror (D-setl x x₁) (D-setl x₂ x₃) r
      = r
    
    mirror (D-inr p) (D-inr q) (D-inr r)
      = D-inr (mirror p q r)
    mirror (D-inr p) (D-inr q) r
      = r 
    
    mirror (D-inr p) (D-setr x x₁) r
      = r
    mirror (D-setr x x₁) (D-inr q) r
      = r
    mirror (D-setr x x₁) (D-setr x₂ x₃) r
      = r
    
    mirror (D-inl p) (D-inr q) r = r
    mirror (D-inl p) (D-setr x x₁) r = r
    mirror (D-inr p) (D-inl q) r = r
    mirror (D-inr p) (D-setl x x₁) r = r
    mirror (D-setl x x₁) (D-inr q) r = r
    mirror (D-setl x x₁) (D-setr x₂ x₃) r = r
    mirror (D-setr x x₁) (D-inl q) r = r
    mirror (D-setr x x₁) (D-setl x₂ x₃) r = r
    
    
    mirror (D-pair p p₁) (D-pair q q₁) (D-pair r r₁)
      = D-pair (mirror p q r) (mirror p₁ q₁ r₁)
    mirror (D-pair p p₁) (D-pair q q₁) (D-A x) = D-A x
    
    
    mirror (D-def p) (D-def q) (D-def r)
      = D-def (mirror p q r)
    mirror (D-def p) (D-def q) (D-A x₁)
      = D-A x₁
    
    mirror (D-top p) (D-top q) (D-top r)
      = D-top (mirror p q r)
    mirror (D-top p) (D-top q) (D-A x)
      = D-A x
    
    mirror (D-pop p) (D-pop q) (D-pop r)
      = D-pop (mirror p q r)
    mirror (D-pop p) (D-pop q) (D-A x)
      = D-A x

    mirror (D-mu x) (D-mu y) (D-mu r)
      = D-mu (mirrorμ x y r)
    mirror (D-mu x) (D-mu y) (D-A r)
      = D-A r

    mirrorμ [] [] rs = rs
    mirrorμ  _ (Dμ-A x ∷ _) rs = rs
    mirrorμ  (Dμ-A x ∷ _) _ rs = rs

    mirrorμ (Dμ-ins a ∷ ps) [] rs
      = on-tail (mirrorμ ps []) rs
      
    mirrorμ [] (Dμ-ins b ∷ qs) rs
      = on-tail (mirrorμ [] qs) rs

    mirrorμ (Dμ-ins a ∷ ps) (Dμ-ins b ∷ qs) rs
      with a ≟-U b | b ≟-U a
    ...| no  abs | yes k   = ⊥-elim (abs (sym k))
    ...| yes k   | no  abs = ⊥-elim (abs (sym k))
    ...| no _    | no  _
      = on-tail (mirrorμ ps qs) rs
    ...| yes _ | yes _
      = mirrorμ ps qs rs
      
    mirrorμ (Dμ-ins a ∷ ps) (Dμ-del x ∷ qs) rs
      = on-tail (mirrorμ ps (Dμ-del x ∷ qs)) rs
      
    mirrorμ (Dμ-ins a ∷ ps) (Dμ-dwn x ∷ qs) rs
      = on-tail (mirrorμ ps (Dμ-dwn x ∷ qs)) rs
      
    mirrorμ (Dμ-dwn x ∷ ps) (Dμ-ins b ∷ qs) rs
      = on-tail (mirrorμ (Dμ-dwn x ∷ ps) qs) rs
                      
    mirrorμ (Dμ-del x ∷ ps) (Dμ-ins b ∷ qs) rs
      = on-tail (mirrorμ (Dμ-del x ∷ ps) qs) rs
      
    mirrorμ (Dμ-dwn x ∷ ps) (Dμ-dwn y ∷ qs) rs
      = hd-tail ((λ { (Dμ-dwn k) → Dμ-dwn (mirror x y k) ; k → k }))
                (mirrorμ ps qs) rs
                      
    mirrorμ (Dμ-dwn x ∷ ps) (Dμ-del y ∷ qs) rs
      with Is-diff-id? x
    ...| no  _ = on-tail (mirrorμ ps qs) rs
    ...| yes _ = mirrorμ ps qs (tail rs)
    
    mirrorμ (Dμ-del x ∷ ps) (Dμ-del y ∷ qs) rs
      = mirrorμ ps qs rs
                     
    mirrorμ (Dμ-del x ∷ ps) (Dμ-dwn y ∷ qs) rs
      with Is-diff-id? y
    ...| no  _ = on-tail (mirrorμ ps qs) rs
    ...| yes _ = Dμ-del x ∷ mirrorμ ps qs rs
    
    mirrorμ [] (Dμ-del x ∷ qs) rs
      = rs
    mirrorμ [] (Dμ-dwn x ∷ qs) rs
      = rs
    mirrorμ (Dμ-del x ∷ ps) [] rs
      = rs
    mirrorμ (Dμ-dwn x ∷ ps) [] rs
      = rs
\end{code}
