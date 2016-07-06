\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Patches.D
open import Diffing.Patches.Properties.WellFormed
open import Diffing.Patches.Properties.Sequential
open import Diffing.Patches.Cost

module Diffing.Patches.Composition (Δ : Cost) where

  open import Diffing.Diff Δ
\end{code}

\begin{code}
  mutual
\end{code}
\begin{code}
    comp : {n : ℕ}{t : T n}{ty : U n}
         → (p q : Patch t ty)(hip : p ⟶ q)
         → Patch t ty

    compμ : {n : ℕ}{t : T n}{ty : U (suc n)}
          → (p q : Patchμ t ty)(hip : p ⟶μ q)
          → Patchμ t ty
         
    comp (D-A ()) q hip
    comp p (D-A ()) hip
    comp D-unit D-unit hip = D-unit
    comp (D-inl p) (D-inl q) hip
      = D-inl (comp p q (⟶-inl p q hip))
    comp (D-inl p) (D-setl x x₁) hip
      = D-setl (D-src-wf (p , (D-inl-wf p (p1 (p1 (⟶-elim hip)))))) x₁
    comp (D-setl x x₁) (D-inr q) hip
      = D-setl x (D-dst-wf (q , D-inr-wf q (p2 (p1 (⟶-elim hip)))))
    comp (D-setl x x₁) (D-setr x₂ x₃) hip
      = D-inl (gdiff x x₃)
    comp (D-inr p) (D-inr q) hip
      = D-inr (comp p q (⟶-inr p q hip))
    comp (D-inr p) (D-setr x x₁) hip
      = D-setr (D-src-wf (p , (D-inr-wf p (p1 (p1 (⟶-elim hip)))))) x₁
    comp (D-setr x x₁) (D-inl q) hip
      = D-setr x (D-dst-wf (q , D-inl-wf q (p2 (p1 (⟶-elim hip)))))
    comp (D-setr x x₁) (D-setl x₂ x₃) hip
      = D-inr (gdiff x x₃)

    
    comp (D-inl p) (D-inr q) hip
      = ⊥-elim (⟶-inl-inr-⊥ p q hip)
    comp (D-inl p) (D-setr x x₁) hip
      = ⊥-elim (⟶-inl-setr-⊥ p x x₁ hip)
    comp (D-inr p) (D-inl q) hip
      = ⊥-elim (⟶-inr-inl-⊥ p q hip)
    comp (D-inr p) (D-setl x x₁) hip
      = ⊥-elim (⟶-inr-setl-⊥ p x x₁ hip)
    comp (D-setl x x₁) (D-inl q) hip
      = ⊥-elim (⟶-setl-inl-⊥ q x x₁ hip)
    comp (D-setl x x₁) (D-setl x₂ x₃) hip
      = ⊥-elim (⟶-setl-setl-⊥ x x₂ x₁ x₃ hip)
    comp (D-setr x x₁) (D-inr q) hip
      = ⊥-elim (⟶-setr-inr-⊥ q x x₁ hip)
    comp (D-setr x x₁) (D-setr x₂ x₃) hip
      = ⊥-elim (⟶-setr-setr-⊥ x x₂ x₁ x₃ hip)
      
    comp (D-pair p p₁) (D-pair q q₁) hip
      = let pq , pq1 = ⟶-pair p q p₁ q₁ hip
         in D-pair (comp p q pq) (comp p₁ q₁ pq1)
    
    comp (D-def p) (D-def q) hip
      = D-def (comp p q (⟶-def p q hip))
    comp (D-top p) (D-top q) hip
      = D-top (comp p q (⟶-top p q hip))
    comp (D-pop p) (D-pop q) hip
      = D-pop (comp p q (⟶-pop p q hip))

    comp (D-mu x) (D-mu y) hip
      = D-mu (compμ x y (⟶-mu x y hip))

    compμ [] [] hip = []
    compμ p (Dμ-A () ∷ q) hip
    compμ (Dμ-A () ∷ p) q hip

    compμ ps (Dμ-ins x ∷ q) hip = Dμ-ins x ∷ compμ ps q (⟶μ-ins-right x ps q hip)


    compμ (Dμ-del x ∷ p) qs hip = Dμ-del x ∷ compμ p qs (⟶μ-del-left x p qs hip)
    
    compμ (Dμ-ins x ∷ p) (Dμ-del y ∷ q) hip
      = let x≡y , pq = ⟶μ-ins-del x y p q hip
         in compμ p q pq


    compμ (Dμ-ins x ∷ p) (Dμ-dwn y ∷ q) hip
      = let sy≡x , pq = ⟶μ-ins-dwn x y p q hip
            wy , _ = Dμ-dwn-wf y q (p2 (p1 (⟶μ-elim hip)))
         in Dμ-ins (D-dst-wf (y , wy)) ∷ compμ p q pq
    
    compμ (Dμ-dwn x ∷ p) (Dμ-dwn y ∷ q) hip
      = let xy , pq = ⟶μ-dwn-dwn x y p q hip
         in Dμ-dwn (comp x y xy) ∷ compμ p q pq


    compμ (Dμ-dwn x ∷ p) (Dμ-del y ∷ q) hip
      = let wx , dx≡y , pq = ⟶μ-dwn-del x y p q hip
         in Dμ-del (D-src-wf (x , wx)) ∷ compμ p q pq

    compμ [] (Dμ-del x ∷ q) hip
      = ⊥-elim (⟶μ-[]-del-⊥ x q hip)
    compμ [] (Dμ-dwn x ∷ q) hip
      = ⊥-elim (⟶μ-[]-dwn-⊥ x q hip)
    compμ (Dμ-ins x ∷ p) [] hip
      = ⊥-elim (⟶μ-ins-[]-⊥ x p hip)
    compμ (Dμ-dwn x ∷ q) [] hip
      = ⊥-elim (⟶μ-dwn-[]-⊥ x q hip)
\end{code}


\begin{code}
  mutual
\end{code}
%<*comp-src-lemma-type>
\begin{code}
      comp-src-lemma : {n : ℕ}{t : T n}{ty : U n}
                     → (p q : Patch t ty)(hip : p ⟶ q)
                     → D-src (comp p q hip) ≡ D-src p
\end{code}
%</comp-src-lemma-type>
%<*comp-mu-src-lemma-type>
\begin{code}
      compμ-src-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
                      → (p q : Patchμ t ty)(hip : p ⟶μ q)
                      → Dμ-src (compμ p q hip) ≡ Dμ-src p
\end{code}
%</comp-mu-src-lemma-type>
\begin{code}
      comp-src-lemma (D-A ()) q hip
      comp-src-lemma p (D-A ()) hip
      comp-src-lemma D-unit D-unit hip = refl
      comp-src-lemma (D-inl p) (D-inl q) hip
        = cong (_<M>_ inl) (comp-src-lemma p q (⟶-inl p q hip))
      comp-src-lemma (D-inl p) (D-setl x x₁) hip
        = sym (<M>-intro (D-src-lemma p (D-inl-wf p (p1 (p1 (⟶-elim hip))))))
      comp-src-lemma (D-setl x x₁) (D-inr q) hip
        = refl
      comp-src-lemma (D-setl x x₁) (D-setr x₂ x₃) hip
        = <M>-intro (gdiff-src-lemma x x₃)
      comp-src-lemma (D-inr p) (D-inr q) hip
        = cong (_<M>_ inr) (comp-src-lemma p q (⟶-inr p q hip))
      comp-src-lemma (D-inr p) (D-setr x x₁) hip
        = sym (<M>-intro (D-src-lemma p (D-inr-wf p (p1 (p1 (⟶-elim hip))))))
      comp-src-lemma (D-setr x x₁) (D-inl q) hip
        = refl
      comp-src-lemma (D-setr x x₁) (D-setl x₂ x₃) hip
        = <M>-intro (gdiff-src-lemma x x₃)


      comp-src-lemma (D-inl p) (D-inr q) hip
        = ⊥-elim (⟶-inl-inr-⊥ p q hip)
      comp-src-lemma (D-inl p) (D-setr x x₁) hip
        = ⊥-elim (⟶-inl-setr-⊥ p x x₁ hip)
      comp-src-lemma (D-inr p) (D-inl q) hip
        = ⊥-elim (⟶-inr-inl-⊥ p q hip)
      comp-src-lemma (D-inr p) (D-setl x x₁) hip
        = ⊥-elim (⟶-inr-setl-⊥ p x x₁ hip)
      comp-src-lemma (D-setl x x₁) (D-inl q) hip
        = ⊥-elim (⟶-setl-inl-⊥ q x x₁ hip)
      comp-src-lemma (D-setl x x₁) (D-setl x₂ x₃) hip
        = ⊥-elim (⟶-setl-setl-⊥ x x₂ x₁ x₃ hip)
      comp-src-lemma (D-setr x x₁) (D-inr q) hip
        = ⊥-elim (⟶-setr-inr-⊥ q x x₁ hip)
      comp-src-lemma (D-setr x x₁) (D-setr x₂ x₃) hip
        = ⊥-elim (⟶-setr-setr-⊥ x x₂ x₁ x₃ hip)

      comp-src-lemma (D-pair p p₁) (D-pair q q₁) hip
        with ⟶-pair p q p₁ q₁ hip
      ...| pq , pq1
        rewrite comp-src-lemma p q pq
              | comp-src-lemma p₁ q₁ pq1
              = refl

      comp-src-lemma (D-def p) (D-def q) hip
        = cong (_<M>_ red) (comp-src-lemma p q (⟶-def p q hip))
      comp-src-lemma (D-top p) (D-top q) hip
        = cong (_<M>_ top) (comp-src-lemma p q (⟶-top p q hip))
      comp-src-lemma (D-pop p) (D-pop q) hip
        = cong (_<M>_ pop) (comp-src-lemma p q (⟶-pop p q hip))

      comp-src-lemma (D-mu x) (D-mu y) hip
        rewrite compμ-src-lemma x y (⟶-mu x y hip)
          = refl

      compμ-src-lemma [] [] hip = refl
      compμ-src-lemma p (Dμ-A () ∷ q) hip
      compμ-src-lemma (Dμ-A () ∷ p) q hip

      compμ-src-lemma [] (Dμ-ins x ∷ q) hip
        =  compμ-src-lemma [] q (⟶μ-ins-right x [] q hip)
      compμ-src-lemma (Dμ-ins x ∷ ps) (Dμ-ins y ∷ q) hip
        = compμ-src-lemma (Dμ-ins x ∷ ps) q (⟶μ-ins-right y (Dμ-ins x ∷ ps) q hip)
      compμ-src-lemma (Dμ-del x ∷ ps) (Dμ-ins y ∷ q) hip
        = compμ-src-lemma (Dμ-del x ∷ ps) q (⟶μ-ins-right y (Dμ-del x ∷ ps) q hip) 
      compμ-src-lemma (Dμ-dwn x ∷ ps) (Dμ-ins y ∷ q) hip
        = compμ-src-lemma (Dμ-dwn x ∷ ps) q (⟶μ-ins-right y (Dμ-dwn x ∷ ps) q hip)

      compμ-src-lemma (Dμ-del x ∷ p) [] hip
        rewrite compμ-src-lemma p [] (⟶μ-del-left x p [] hip)
          = refl 
      compμ-src-lemma (Dμ-del x ∷ p) (Dμ-del y ∷ qs) hip
        rewrite compμ-src-lemma p (Dμ-del y ∷ qs) (⟶μ-del-left x p (Dμ-del y ∷ qs) hip)
          = refl
      compμ-src-lemma (Dμ-del x ∷ p) (Dμ-dwn y ∷ qs) hip
        rewrite compμ-src-lemma p (Dμ-dwn y ∷ qs) (⟶μ-del-left x p (Dμ-dwn y ∷ qs) hip)
          = refl

      compμ-src-lemma (Dμ-ins x ∷ p) (Dμ-del y ∷ q) hip
        = let x≡y , pq = ⟶μ-ins-del x y p q hip
           in compμ-src-lemma p q pq 


      compμ-src-lemma (Dμ-ins x ∷ p) (Dμ-dwn y ∷ q) hip
        = let sy≡x , pq = ⟶μ-ins-dwn x y p q hip
              wy , _ = Dμ-dwn-wf y q (p2 (p1 (⟶μ-elim hip)))
           in compμ-src-lemma p q pq

      compμ-src-lemma (Dμ-dwn x ∷ p) (Dμ-dwn y ∷ q) hip
        with ⟶μ-dwn-dwn x y p q hip
      ...| xy , pq
        rewrite compμ-src-lemma p q pq
              | comp-src-lemma x y xy
              = refl


      compμ-src-lemma (Dμ-dwn x ∷ p) (Dμ-del y ∷ q) hip
        with ⟶μ-dwn-del x y p q hip
      ...| wx , dx≡y , pq
        rewrite compμ-src-lemma p q pq
              | D-src-lemma x wx
              = refl
 
      compμ-src-lemma [] (Dμ-del x ∷ q) hip
        = ⊥-elim (⟶μ-[]-del-⊥ x q hip)
      compμ-src-lemma [] (Dμ-dwn x ∷ q) hip
        = ⊥-elim (⟶μ-[]-dwn-⊥ x q hip)
      compμ-src-lemma (Dμ-ins x ∷ p) [] hip
        = ⊥-elim (⟶μ-ins-[]-⊥ x p hip)
      compμ-src-lemma (Dμ-dwn x ∷ q) [] hip
        = ⊥-elim (⟶μ-dwn-[]-⊥ x q hip)
\end{code}

\begin{code}
  mutual
\end{code}
%<*comp-dst-lemma-type>
\begin{code}
      comp-dst-lemma : {n : ℕ}{t : T n}{ty : U n}
                     → (p q : Patch t ty)(hip : p ⟶ q)
                     → D-dst (comp p q hip) ≡ D-dst q
\end{code}
%</comp-dst-lemma-type>
%<*comp-mu-dst-lemma-type>
\begin{code}
      compμ-dst-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
                      → (p q : Patchμ t ty)(hip : p ⟶μ q)
                      → Dμ-dst (compμ p q hip) ≡ Dμ-dst q
\end{code}
%</comp-mu-dst-lemma-type>
\begin{code}
      comp-dst-lemma (D-A ()) q hip
      comp-dst-lemma p (D-A ()) hip
      comp-dst-lemma D-unit D-unit hip = refl
      comp-dst-lemma (D-inl p) (D-inl q) hip
        = cong (_<M>_ inl) (comp-dst-lemma p q (⟶-inl p q hip))
      comp-dst-lemma (D-inl p) (D-setl x x₁) hip
        = refl
      comp-dst-lemma (D-setl x x₁) (D-inr q) hip
        = sym (<M>-intro (D-dst-lemma q (D-inr-wf q (p2 (p1 (⟶-elim hip))))))
      comp-dst-lemma (D-setl x x₁) (D-setr x₂ x₃) hip
        = <M>-intro (gdiff-dst-lemma x x₃)
      comp-dst-lemma (D-inr p) (D-inr q) hip
        = cong (_<M>_ inr) (comp-dst-lemma p q (⟶-inr p q hip))
      comp-dst-lemma (D-inr p) (D-setr x x₁) hip
        = refl
      comp-dst-lemma (D-setr x x₁) (D-inl q) hip
        = sym (<M>-intro (D-dst-lemma q (D-inl-wf q (p2 (p1 (⟶-elim hip))))))
      comp-dst-lemma (D-setr x x₁) (D-setl x₂ x₃) hip
        = <M>-intro (gdiff-dst-lemma x x₃)


      comp-dst-lemma (D-inl p) (D-inr q) hip
        = ⊥-elim (⟶-inl-inr-⊥ p q hip)
      comp-dst-lemma (D-inl p) (D-setr x x₁) hip
        = ⊥-elim (⟶-inl-setr-⊥ p x x₁ hip)
      comp-dst-lemma (D-inr p) (D-inl q) hip
        = ⊥-elim (⟶-inr-inl-⊥ p q hip)
      comp-dst-lemma (D-inr p) (D-setl x x₁) hip
        = ⊥-elim (⟶-inr-setl-⊥ p x x₁ hip)
      comp-dst-lemma (D-setl x x₁) (D-inl q) hip
        = ⊥-elim (⟶-setl-inl-⊥ q x x₁ hip)
      comp-dst-lemma (D-setl x x₁) (D-setl x₂ x₃) hip
        = ⊥-elim (⟶-setl-setl-⊥ x x₂ x₁ x₃ hip)
      comp-dst-lemma (D-setr x x₁) (D-inr q) hip
        = ⊥-elim (⟶-setr-inr-⊥ q x x₁ hip)
      comp-dst-lemma (D-setr x x₁) (D-setr x₂ x₃) hip
        = ⊥-elim (⟶-setr-setr-⊥ x x₂ x₁ x₃ hip)

      comp-dst-lemma (D-pair p p₁) (D-pair q q₁) hip
        with ⟶-pair p q p₁ q₁ hip
      ...| pq , pq1
        rewrite comp-dst-lemma p q pq
              | comp-dst-lemma p₁ q₁ pq1
              = refl

      comp-dst-lemma (D-def p) (D-def q) hip
        = cong (_<M>_ red) (comp-dst-lemma p q (⟶-def p q hip))
      comp-dst-lemma (D-top p) (D-top q) hip
        = cong (_<M>_ top) (comp-dst-lemma p q (⟶-top p q hip))
      comp-dst-lemma (D-pop p) (D-pop q) hip
        = cong (_<M>_ pop) (comp-dst-lemma p q (⟶-pop p q hip))

      comp-dst-lemma (D-mu x) (D-mu y) hip
        rewrite compμ-dst-lemma x y (⟶-mu x y hip)
          = refl

      compμ-dst-lemma [] [] hip = refl
      compμ-dst-lemma p (Dμ-A () ∷ q) hip
      compμ-dst-lemma (Dμ-A () ∷ p) q hip

      compμ-dst-lemma [] (Dμ-ins x ∷ q) hip
        rewrite compμ-dst-lemma [] q (⟶μ-ins-right x [] q hip)
          = refl
      compμ-dst-lemma (Dμ-ins x ∷ ps) (Dμ-ins y ∷ q) hip
        rewrite compμ-dst-lemma (Dμ-ins x ∷ ps) q (⟶μ-ins-right y (Dμ-ins x ∷ ps) q hip)
          = refl
      compμ-dst-lemma (Dμ-del x ∷ ps) (Dμ-ins y ∷ q) hip
        rewrite compμ-dst-lemma (Dμ-del x ∷ ps) q (⟶μ-ins-right y (Dμ-del x ∷ ps) q hip)
          = refl
      compμ-dst-lemma (Dμ-dwn x ∷ ps) (Dμ-ins y ∷ q) hip
        rewrite compμ-dst-lemma (Dμ-dwn x ∷ ps) q (⟶μ-ins-right y (Dμ-dwn x ∷ ps) q hip)
          = refl

      compμ-dst-lemma (Dμ-del x ∷ p) [] hip
        rewrite compμ-dst-lemma p [] (⟶μ-del-left x p [] hip)
          = refl 
      compμ-dst-lemma (Dμ-del x ∷ p) (Dμ-del y ∷ qs) hip
        rewrite compμ-dst-lemma p (Dμ-del y ∷ qs) (⟶μ-del-left x p (Dμ-del y ∷ qs) hip)
          = refl
      compμ-dst-lemma (Dμ-del x ∷ p) (Dμ-dwn y ∷ qs) hip
        rewrite compμ-dst-lemma p (Dμ-dwn y ∷ qs) (⟶μ-del-left x p (Dμ-dwn y ∷ qs) hip)
          = refl

      compμ-dst-lemma (Dμ-ins x ∷ p) (Dμ-del y ∷ q) hip
        = let x≡y , pq = ⟶μ-ins-del x y p q hip
           in compμ-dst-lemma p q pq 


      compμ-dst-lemma (Dμ-ins x ∷ p) (Dμ-dwn y ∷ q) hip
        with ⟶μ-ins-dwn x y p q hip | Dμ-dwn-wf y q (p2 (p1 (⟶μ-elim hip)))
      ...| sy≡x , pq | wy , _
        rewrite compμ-dst-lemma p q pq
              | D-dst-lemma y wy
              = refl

      compμ-dst-lemma (Dμ-dwn x ∷ p) (Dμ-dwn y ∷ q) hip
        with ⟶μ-dwn-dwn x y p q hip
      ...| xy , pq
        rewrite compμ-dst-lemma p q pq
              | comp-dst-lemma x y xy
              = refl


      compμ-dst-lemma (Dμ-dwn x ∷ p) (Dμ-del y ∷ q) hip
        with ⟶μ-dwn-del x y p q hip
      ...| wx , dx≡y , pq
        rewrite compμ-dst-lemma p q pq
              | D-dst-lemma x wx
              = refl
 
      compμ-dst-lemma [] (Dμ-del x ∷ q) hip
        = ⊥-elim (⟶μ-[]-del-⊥ x q hip)
      compμ-dst-lemma [] (Dμ-dwn x ∷ q) hip
        = ⊥-elim (⟶μ-[]-dwn-⊥ x q hip)
      compμ-dst-lemma (Dμ-ins x ∷ p) [] hip
        = ⊥-elim (⟶μ-ins-[]-⊥ x p hip)
      compμ-dst-lemma (Dμ-dwn x ∷ q) [] hip
        = ⊥-elim (⟶μ-dwn-[]-⊥ x q hip)
\end{code}
