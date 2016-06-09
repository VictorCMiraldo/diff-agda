\begin{code}
open import Prelude
open import Diffing.Universe

open import Diffing.Patches.D
open import Diffing.Patches.Functor
open import Diffing.Patches.Id
open import Diffing.Patches.Properties.WellFounded
open import Diffing.Patches.Properties.Alignment
open import Diffing.Conflicts.C
open import Diffing.Residual

module Diffing.Residual.Symmetry where
\end{code}

\begin{code}
  mutual
\end{code}
%<*res-symmetry-type>
\begin{code}
    res-symmetry
      : {n : ℕ}{t : T n}{ty : U n}
      → (p q : Patch t ty)(hip : p || q)
      → Σ ({A : TU→Set} → D A t ty → D A t ty)
          (λ f → res p q hip ≡ D-map C-sym (f (res q p (||-sym hip))))
\end{code}
%</res-symmetry-type>
%<*res-mu-symmetry-type>
\begin{code}
    resμ-symmetry
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (p q : Patchμ t ty)(hip : p ||μ q)
      → Σ ({A : TU→Set} → List (Dμ A t ty) → List (Dμ A t ty))
          (λ f → resμ p q hip ≡ Dμ-map C-sym (f (resμ q p (||μ-sym hip))))
\end{code}
%</res-mu-symmetry-type>
\begin{code}
    res-symmetry (D-A ()) q hip
    res-symmetry p (D-A ()) hip
    res-symmetry D-unit D-unit hip
      = id , refl
    res-symmetry (D-inl p) (D-inl q) hip
      with res-symmetry p q (||-inl-elim p q hip)
    ...| f , rec rewrite rec
      = (λ { (D-inl k) → D-inl (f k) ; k → k })
      , cong (λ P → D-inl (D-map C-sym (f (res q p P))))
             (||-pi (||-sym (||-inl-elim p q hip))
                    (||-inl-elim q p (||-sym hip)))
    res-symmetry (D-inl p) (D-setl x y) hip
      with Is-diff-id? p
    ...| yes _ = id , refl
    ...| no  _
       = id
       , cong (λ P → D-A (UpdUpd (inl x) (D-dst-wf (D-inl p , P)) (inr y)))
              (WF-pi {A = ⊥ₚ} {p = D-inl p}
                (p1 (p1 (||-elim hip))) (p2 (p1 (||-elim (||-sym hip)))))     
    res-symmetry (D-setl x y) (D-inl q) hip
      with Is-diff-id? q
    ...| yes _ = id , refl
    ...| no  _
       = id
       , cong (λ P → D-A (UpdUpd (inl x) (inr y) (D-dst-wf (D-inl q , P))))
              (WF-pi {A = ⊥ₚ} {p = D-inl q}
                (p2 (p1 (||-elim hip))) (p1 (p1 (||-elim (||-sym hip)))))  
    res-symmetry (D-setl x y) (D-setl w z) hip
      with z ≟-U y | y ≟-U z
    ...| no  abs | yes k   = ⊥-elim (abs (sym k))
    ...| yes k   | no  abs = ⊥-elim (abs (sym k))
    ...| no _    | no  _
      rewrite ||-setl-elim x w y z hip = id , refl
    ...| yes y≡z | yes _
      rewrite y≡z = id , cong D-inr (sym (D-map-cast C-sym (gdiff-id y)))
    res-symmetry (D-inr p) (D-inr q) hip
      with res-symmetry p q (||-inr-elim p q hip)
    ...| f , rec rewrite rec
      = (λ { (D-inr k) → D-inr (f k) ; k → k })
      , cong (λ P → D-inr (D-map C-sym (f (res q p P))))
             (||-pi (||-sym (||-inr-elim p q hip))
                    (||-inr-elim q p (||-sym hip)))
    res-symmetry (D-inr p) (D-setr x y) hip
      with Is-diff-id? p
    ...| yes _ = id , refl
    ...| no  _
       = id
       , cong (λ P → D-A (UpdUpd (inr x) (D-dst-wf (D-inr p , P)) (inl y)))
              (WF-pi {A = ⊥ₚ} {p = D-inr p}
                (p1 (p1 (||-elim hip))) (p2 (p1 (||-elim (||-sym hip))))) 
    res-symmetry (D-setr x y) (D-inr q) hip
      with Is-diff-id? q
    ...| yes _ = id , refl
    ...| no  _
       = id
       , cong (λ P → D-A (UpdUpd (inr x) (inl y) (D-dst-wf (D-inr q , P))))
              (WF-pi {A = ⊥ₚ} {p = D-inr q}
                (p2 (p1 (||-elim hip))) (p1 (p1 (||-elim (||-sym hip))))) 
    res-symmetry (D-setr x y) (D-setr w z) hip
      with z ≟-U y | y ≟-U z
    ...| no  abs | yes k   = ⊥-elim (abs (sym k))
    ...| yes k   | no  abs = ⊥-elim (abs (sym k))
    ...| no _    | no  _
      rewrite ||-setr-elim x w y z hip = id , refl
    ...| yes y≡z | yes _
      rewrite y≡z = id , cong D-inl (sym (D-map-cast C-sym (gdiff-id y)))
      
    res-symmetry (D-inl p) (D-inr q) hip
      = ⊥-elim (||-inl-inr-⊥ p q hip)
    res-symmetry (D-inl p) (D-setr x x₁) hip
      = ⊥-elim (||-inl-setr-⊥ p x₁ x hip)
    res-symmetry (D-inr p) (D-inl q) hip
      = ⊥-elim (||-inl-inr-⊥ q p (||-sym hip))
    res-symmetry (D-inr p) (D-setl x x₁) hip
      = ⊥-elim (||-inr-setl-⊥ p x x₁ hip)
    res-symmetry (D-setl xa xb) (D-inr q) hip
      = ⊥-elim (||-inr-setl-⊥ q xa xb (||-sym hip))
    res-symmetry (D-setl xa xb) (D-setr xc xd) hip
      = ⊥-elim (||-setl-setr-⊥ xa xd xb xc hip)
    res-symmetry (D-setr xa xb) (D-inl q) hip
      = ⊥-elim (||-inl-setr-⊥ q xb xa (||-sym hip))
    res-symmetry (D-setr xa xb) (D-setl xc xd) hip
      = ⊥-elim (||-setl-setr-⊥ xc xb xd xa (||-sym hip))
      
    res-symmetry (D-pair p p₁) (D-pair q q₁) hip
      with res-symmetry p q (p1 (||-pair-elim p q p₁ q₁ hip))
    ...| f₀ , rec₀
      with res-symmetry p₁ q₁ (p2 (||-pair-elim p q p₁ q₁ hip))
    ...| f₁ , rec₁
      rewrite rec₀ | rec₁
        = (λ { (D-pair m n) → D-pair (f₀ m) (f₁ n) ; k → k })
        , cong₂ (λ P Q → D-pair (D-map C-sym (f₀ (res q p P))) (D-map C-sym (f₁ (res q₁ p₁ Q))))
                (||-pi (||-sym (p1 (||-pair-elim p q p₁ q₁ hip)))
                       (p1 (||-pair-elim q p q₁ p₁ (||-sym hip))))
                (||-pi (||-sym (p2 (||-pair-elim p q p₁ q₁ hip)))
                       (p2 (||-pair-elim q p q₁ p₁ (||-sym hip))))
    
    res-symmetry (D-def p) (D-def q) hip
      with res-symmetry p q (||-def-elim p q hip)
    ...| f , rec rewrite rec
      = (λ { (D-def k) → D-def (f k) ; k → k })
      , cong (λ P → D-def (D-map C-sym (f (res q p P))))
             (||-pi (||-sym (||-def-elim p q hip))
                    (||-def-elim q p (||-sym hip)))
    res-symmetry (D-top p) (D-top q) hip
      with res-symmetry p q (||-top-elim p q hip)
    ...| f , rec rewrite rec
      = (λ { (D-top k) → D-top (f k) ; k → k })
      , cong (λ P → D-top (D-map C-sym (f (res q p P))))
             (||-pi (||-sym (||-top-elim p q hip))
                    (||-top-elim q p (||-sym hip)))
    res-symmetry (D-pop p) (D-pop q) hip
      with res-symmetry p q (||-pop-elim p q hip)
    ...| f , rec rewrite rec
      = (λ { (D-pop k) → D-pop (f k) ; k → k })
      , cong (λ P → D-pop (D-map C-sym (f (res q p P))))
             (||-pi (||-sym (||-pop-elim p q hip))
                    (||-pop-elim q p (||-sym hip)))
                    
    res-symmetry (D-mu x)  (D-mu y) hip
      with resμ-symmetry x y (||-mu-elim x y hip)
    ...| f , rec rewrite rec
      = (λ { (D-mu k) → D-mu (f k) ; k → k })
      , cong (λ P → D-mu (Dμ-map C-sym (f (resμ y x P))))
             (||μ-pi (||μ-sym (||-mu-elim x y hip))
                     (||-mu-elim y x (||-sym hip))) 

    resμ-symmetry [] [] hip = id , refl
    resμ-symmetry  _ (Dμ-A () ∷ _) _
    resμ-symmetry  (Dμ-A () ∷ _) _ _

    resμ-symmetry (Dμ-ins a ∷ ps) [] hip
      with resμ-symmetry ps [] (||μ-ins-elim a ps [] hip)
    ...| f , rec rewrite rec
      = on-tail f
      , cong (λ P → Dμ-A (GrowL a) ∷ Dμ-map C-sym (f (resμ [] ps P)))
              (||μ-pi (||μ-sym (||μ-ins-elim a ps [] hip))
                      (||μ-sym (||μ-ins-elim a ps [] (||μ-sym (||μ-sym hip)))))
    resμ-symmetry [] (Dμ-ins b ∷ qs) hip
      with resμ-symmetry [] qs (||μ-sym (||μ-ins-elim b qs [] (||μ-sym hip)))
    ...| f , rec rewrite rec
      = on-tail f
      , cong (λ P → Dμ-A (GrowR b) ∷ Dμ-map C-sym (f (resμ qs [] P)))
             (||μ-pi (||μ-sym (||μ-sym (||μ-ins-elim b qs [] (||μ-sym hip))))
                     (||μ-ins-elim b qs [] (||μ-sym hip)))

    resμ-symmetry (Dμ-ins a ∷ ps) (Dμ-ins b ∷ qs) hip
      with a ≟-U b | b ≟-U a
    ...| no  abs | yes k   = ⊥-elim (abs (sym k))
    ...| yes k   | no  abs = ⊥-elim (abs (sym k))
    ...| no _    | no  _
      with resμ-symmetry ps qs (||μ-ins-ins-elim a b ps qs hip)
    ...| f , rec rewrite rec
      = on-tail f , cong (λ P → Dμ-A (GrowLR a b) ∷ Dμ-map C-sym (f (resμ qs ps P)))
                         (||μ-pi (||μ-sym (||μ-ins-ins-elim a b ps qs hip))
                                 (||μ-ins-ins-elim b a qs ps (||μ-sym hip)))
    resμ-symmetry (Dμ-ins a ∷ ps) (Dμ-ins b ∷ qs) hip
      | yes a≡b | yes _
      rewrite a≡b with resμ-symmetry ps qs (||μ-ins-ins-elim b b ps qs hip)
    ...| f , rec rewrite rec
      = f , cong (λ P → Dμ-map C-sym (f (resμ qs ps P)))
                 (||μ-pi (||μ-sym (||μ-ins-ins-elim b b ps qs hip))
                         (||μ-ins-ins-elim b b qs ps (||μ-sym hip))) 
    resμ-symmetry (Dμ-ins a ∷ ps) (Dμ-del x ∷ qs) hip
      with resμ-symmetry ps (Dμ-del x ∷ qs) (||μ-ins-elim a ps (Dμ-del x ∷ qs) hip)
    ...| f , rec rewrite rec
       = on-tail f
       , cong (λ P → Dμ-A (GrowL a) ∷ Dμ-map C-sym (f (resμ (Dμ-del x ∷ qs) ps P)))
              (||μ-pi (||μ-sym (||μ-ins-elim a ps (Dμ-del x ∷ qs) hip))
                      (||μ-sym (||μ-ins-elim a ps (Dμ-del x ∷ qs) (||μ-sym (||μ-sym hip)))))
    resμ-symmetry (Dμ-ins a ∷ ps) (Dμ-dwn x ∷ qs) hip
      with resμ-symmetry ps (Dμ-dwn x ∷ qs) (||μ-ins-elim a ps (Dμ-dwn x ∷ qs) hip)
    ...| f , rec rewrite rec
       = on-tail f
       , cong (λ P → Dμ-A (GrowL a) ∷ Dμ-map C-sym (f (resμ (Dμ-dwn x ∷ qs) ps P)))
              (||μ-pi (||μ-sym (||μ-ins-elim a ps (Dμ-dwn x ∷ qs) hip))
                      (||μ-sym (||μ-ins-elim a ps (Dμ-dwn x ∷ qs) (||μ-sym (||μ-sym hip)))))
    resμ-symmetry (Dμ-dwn x ∷ ps) (Dμ-ins b ∷ qs) hip
      with resμ-symmetry (Dμ-dwn x ∷ ps) qs
                (||μ-sym (||μ-ins-elim b qs (Dμ-dwn x ∷ ps) (||μ-sym hip)))
    ...| f , rec rewrite rec
      = on-tail f
      , cong (λ P → Dμ-A (GrowR b) ∷ Dμ-map C-sym (f (resμ qs (Dμ-dwn x ∷ ps) P)))
              (||μ-pi (||μ-sym (||μ-sym (||μ-ins-elim b qs (Dμ-dwn x ∷ ps) (||μ-sym hip))))
                      (||μ-ins-elim b qs (Dμ-dwn x ∷ ps) (||μ-sym hip))) 
    resμ-symmetry (Dμ-del x ∷ ps) (Dμ-ins b ∷ qs) hip
      with resμ-symmetry (Dμ-del x ∷ ps) qs
                (||μ-sym (||μ-ins-elim b qs (Dμ-del x ∷ ps) (||μ-sym hip)))
    ...| f , rec rewrite rec
      = on-tail f
      , cong (λ P → Dμ-A (GrowR b) ∷ Dμ-map C-sym (f (resμ qs (Dμ-del x ∷ ps) P)))
              (||μ-pi (||μ-sym (||μ-sym (||μ-ins-elim b qs (Dμ-del x ∷ ps) (||μ-sym hip))))
                      (||μ-ins-elim b qs (Dμ-del x ∷ ps) (||μ-sym hip))) 
    resμ-symmetry (Dμ-dwn x ∷ ps) (Dμ-dwn y ∷ qs) hip
      with resμ-symmetry ps qs (p1 (||μ-dwn-dwn-elim x y ps qs hip))
    ...| f , rec rewrite rec
      with res-symmetry x y (p2 (||μ-dwn-dwn-elim x y ps qs hip))
    ...| fx , recx rewrite recx
      = (hd-tail (λ { (Dμ-dwn x) → Dμ-dwn (fx x) ; k → k }) f)
      , cong₂ (λ P Q → Dμ-dwn (D-map C-sym (fx (res y x P))) ∷ Dμ-map C-sym (f (resμ qs ps Q)))
              (||-pi (||-sym (p2 (||μ-dwn-dwn-elim x y ps qs hip)))
                     (p2 (||μ-dwn-dwn-elim y x qs ps (||μ-sym hip))))
              (||μ-pi (||μ-sym (p1 (||μ-dwn-dwn-elim x y ps qs hip)))
                      (p1 (||μ-dwn-dwn-elim y x qs ps (||μ-sym hip))))
                      
    resμ-symmetry (Dμ-dwn x ∷ ps) (Dμ-del y ∷ qs) hip
      with Is-diff-id? x
    resμ-symmetry (Dμ-dwn x ∷ ps) (Dμ-del y ∷ qs) hip | no  _
      with resμ-symmetry ps qs (||μ-dwn-del-elim y x ps qs hip)
    ...| f , rec rewrite rec with ||μ-elim hip | inspect ||μ-elim hip
    ...| ((wps , wqs) , prf) | [ ELIM ]
      rewrite ||μ-elim-sym hip ELIM
       = on-tail f
       , cong₂ (λ P Q → Dμ-A (UpdDel P y) ∷ Dμ-map C-sym (f (resμ qs ps Q)))
               refl
               (||μ-pi (||μ-sym (||μ-dwn-del-elim y x ps qs hip))
                       (||μ-sym (||μ-dwn-del-elim y x ps qs (||μ-sym (||μ-sym hip))))) 
    resμ-symmetry (Dμ-dwn x ∷ ps) (Dμ-del y ∷ qs) hip | yes _
      with resμ-symmetry ps qs (||μ-dwn-del-elim y x ps qs hip)
    ...| f , rec rewrite rec
      = f ∘ tail
      , cong (λ P → Dμ-map C-sym (f (resμ qs ps P)))
             (||μ-pi (||μ-sym (||μ-dwn-del-elim y x ps qs hip))
                     (||μ-sym (||μ-dwn-del-elim y x ps qs (||μ-sym (||μ-sym hip))))) 
    
    resμ-symmetry (Dμ-del x ∷ ps) (Dμ-del y ∷ qs) hip
      with resμ-symmetry ps qs (p1 (||μ-del-del-elim y x ps qs hip))
    ...| f , rec rewrite rec
      = f
      , cong (λ P → Dμ-map C-sym (f (resμ qs ps P)))
             (||μ-pi (||μ-sym (p1 (||μ-del-del-elim y x ps qs hip)))
                     (p1 (||μ-del-del-elim x y qs ps (||μ-sym hip))))
                     
    resμ-symmetry (Dμ-del x ∷ ps) (Dμ-dwn y ∷ qs) hip
      with Is-diff-id? y
    resμ-symmetry (Dμ-del x ∷ ps) (Dμ-dwn y ∷ qs) hip | no _
      with resμ-symmetry ps qs (||μ-sym (||μ-dwn-del-elim x y qs ps (||μ-sym hip)))
    ...| f , rec rewrite rec with ||μ-elim hip | inspect ||μ-elim hip
    ...| ((wps , wqs) , prf) | [ ELIM ]
      rewrite ||μ-elim-sym hip ELIM
       = on-tail f
       , cong₂ (λ P Q → Dμ-A (DelUpd x P) ∷ Dμ-map C-sym (f (resμ qs ps Q)))
               refl
               (||μ-pi (||μ-sym (||μ-sym (||μ-dwn-del-elim x y qs ps (||μ-sym hip))))
                       (||μ-dwn-del-elim x y qs ps (||μ-sym hip))) 
    resμ-symmetry (Dμ-del x ∷ ps) (Dμ-dwn y ∷ qs) hip | yes _
      with resμ-symmetry ps qs (||μ-sym (||μ-dwn-del-elim x y qs ps (||μ-sym hip)))
    ...| f , rec rewrite rec
      = (_∷_ (Dμ-del x)) ∘ f
      , cong (λ P → Dμ-del x ∷ Dμ-map C-sym (f (resμ qs ps P)))
             (||μ-pi (||μ-sym (||μ-sym (||μ-dwn-del-elim x y qs ps (||μ-sym hip))))
                     (||μ-dwn-del-elim x y qs ps (||μ-sym hip)))
    
    
    resμ-symmetry [] (Dμ-del x ∷ qs) hip
      = ⊥-elim (||μ-[]-del-⊥ x qs hip)
    resμ-symmetry [] (Dμ-dwn x ∷ qs) hip
      = ⊥-elim (||μ-[]-dwn-⊥ x qs hip)
    resμ-symmetry (Dμ-del x ∷ ps) [] hip
      = ⊥-elim (||μ-[]-del-⊥ x ps (||μ-sym hip))
    resμ-symmetry (Dμ-dwn x ∷ ps) [] hip
      = ⊥-elim (||μ-[]-dwn-⊥ x ps (||μ-sym hip))
\end{code}
