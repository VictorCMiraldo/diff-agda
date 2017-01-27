\begin{code}
open import Prelude
open import Prelude.ListProperties
  using (∷≡[]→⊥; ∷-inj; lsplit-elim; map-inj-inj; lhead-elim)
open import Diffing.Universe
open import CF.Properties
  using (plug-spec-fgt; plug-spec-ch)
open import Diffing.Patches.D
open import Diffing.Patches.Properties.WellFormed

module Diffing.Patches.Properties.Sequential where
\end{code}

\begin{code}
  infix 30 _⟶_ _⟶μ_
  
  abstract
    _⟶_ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
        → (p q : D A t ty)
        → Set
    _⟶_ {A} {n} {t} {ty} p q
      = (WF p × WF q) × D-dst p ≡ D-src q

    _⟶μ_ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
        → (p q : List (Dμ A t ty))
        → Set
    _⟶μ_ {A} {n} {t} {ty} p q
      = (WFμ p × WFμ q) × Dμ-dst p ≡ Dμ-src q
\end{code}

\begin{code}
    ⟶-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
      → {p q : D A t ty} → (p ⟶ q)
      → (WF p × WF q) × D-dst p ≡ D-src q
    ⟶-elim hip = hip

    ⟶-intro
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
      → {p q : D A t ty} 
      → (WF p × WF q) × D-dst p ≡ D-src q
      → (p ⟶ q)
    ⟶-intro hip = hip

    ⟶μ-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → {p q : List (Dμ A t ty)} → (p ⟶μ q)
      → (WFμ p × WFμ q) × Dμ-dst p ≡ Dμ-src q
    ⟶μ-elim hip = hip
\end{code}

\begin{code}
    ⟶-pair
        : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
        → (q0 q1 : D A t ty)(r0 r1 : D A t tv)
        → (D-pair q0 r0) ⟶ (D-pair q1 r1)
        → (q0 ⟶ q1) × (r0 ⟶ r1)
    ⟶-pair q0 q1 r0 r1 ((w0 , w1) , prf)
      with D-pair-wf q0 r0 w0
    ...| ((sq0 , dq0) , psq0 , pdq0)
       , ((sr0 , dr0) , psr0 , pdr0)
      with D-pair-wf q1 r1 w1
    ...| ((sq1 , dq1) , psq1 , pdq1)
       , ((sr1 , dr1) , psr1 , pdr1)
      rewrite psq0 | pdq0
            | psr0 | pdr0
            | psq1 | pdq1
            | psr1 | pdr1
            = ((((sq0 , dq0) , refl , refl)
              , ((sq1 , dq1) , refl , refl))
              , (cong just (p1 (inj-, (just-inj prf)))))
            , ((((sr0 , dr0) , refl , refl)
              , ((sr1 , dr1) , refl , refl))
              , (cong just (p2 (inj-, (just-inj prf)))))

    ⟶-inl-setl
        : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
        → (p : D A t ty)(x : ElU ty t)(y : ElU tv t)
        → (D-inl p) ⟶ (D-setl x y)
        → D-dst p ≡ just x
    ⟶-inl-setl p x y ((wp , wxy) , prf)
      with <M>-elim prf
    ...| .x , refl , r2 = r2

    ⟶-setl-inr
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (x : ElU ty t)(y : ElU tv t)(p : D A t tv)
      → (D-setl x y) ⟶ (D-inr p)
      → D-src p ≡ just y
    ⟶-setl-inr x y p ((wxy , wp) , prf)
      with <M>-elim (sym prf)
    ...| .y , refl , r2 = r2

    ⟶-setl-setr
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (x w : ElU ty t)(y z : ElU tv t)
      → (D-setl {A = A} x y) ⟶ (D-setr z w)
      → y ≡ z
    ⟶-setl-setr x w y z ((wxy , wzw) , prf)
      = inj-inr (just-inj prf)

    ⟶-inr-setr
        : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
        → (p : D A t tv)(x : ElU tv t)(y : ElU ty t)
        → (D-inr p) ⟶ (D-setr x y)
        → D-dst p ≡ just x
    ⟶-inr-setr p x y ((wp , wxy) , prf)
      with <M>-elim prf
    ...| .x , refl , r2 = r2

    ⟶-setr-inl
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (x : ElU tv t)(y : ElU ty t)(p : D A t ty)
      → (D-setr x y) ⟶ (D-inl p)
      → D-src p ≡ just y
    ⟶-setr-inl x y p ((wxy , wp) , prf)
      with <M>-elim (sym prf)
    ...| .y , refl , r2 = r2

    ⟶-setr-setl
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (x w : ElU tv t)(y z : ElU ty t)
      → (D-setr {A = A} x y) ⟶ (D-setl z w)
      → y ≡ z
    ⟶-setr-setl x w y z ((wxy , wzw) , prf)
      = inj-inl (just-inj prf)

    ⟶-inl : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
          → (p q : D A t ty)
          → (D-inl {b = tv} p) ⟶ D-inl q
          → p ⟶ q
    ⟶-inl p q ((wp , wq) , prf)
      = (D-inl-wf p wp , D-inl-wf q wq) , <M>-inj inj-inl prf

    ⟶-inr : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
          → (p q : D A t tv)
          → (D-inr {a = ty} p) ⟶ D-inr q
          → p ⟶ q
    ⟶-inr p q ((wp , wq) , prf)
      = (D-inr-wf p wp , D-inr-wf q wq) , <M>-inj inj-inr prf

    ⟶-inl-inr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t ty)(q : D A t tv)
      → (D-inl p) ⟶ (D-inr q)
      → ⊥
    ⟶-inl-inr-⊥ p q ((((sp , dp) , hsp , hdp) , ((sq , dq) , hsq , hdq)) , hip)
      with <M>-elim hdp | <M>-elim hsq
    ...| r0 , r1 , r2 | s0 , s1 , s2
      rewrite r2 | s2 = inl≡inr→⊥ (just-inj hip)

    ⟶-inr-inl-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t tv)(q : D A t ty)
      → (D-inr p) ⟶ (D-inl q)
      → ⊥
    ⟶-inr-inl-⊥ p q ((((sp , dp) , hsp , hdp) , ((sq , dq) , hsq , hdq)) , hip)
      with <M>-elim hdp | <M>-elim hsq
    ...| r0 , r1 , r2 | s0 , s1 , s2
      rewrite r2 | s2 = inl≡inr→⊥ (just-inj (sym hip))

    ⟶-inl-setr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t ty)(x : ElU tv t)(y : ElU ty t)
      → (D-inl p) ⟶ (D-setr x y)
      → ⊥
    ⟶-inl-setr-⊥ p x y (wpq , hip)
      with <M>-elim hip
    ...| r0 , r1 , r2 = inl≡inr→⊥ (sym r1)

    ⟶-inr-setl-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t tv)(x : ElU ty t)(y : ElU tv t)
      → (D-inr p) ⟶ (D-setl x y)
      → ⊥
    ⟶-inr-setl-⊥ p x y (wpq , hip)
      with <M>-elim hip
    ...| r0 , r1 , r2 = inl≡inr→⊥ r1

    ⟶-setl-inl-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t ty)(x : ElU ty t)(y : ElU tv t)
      → (D-setl x y) ⟶ (D-inl p)
      → ⊥
    ⟶-setl-inl-⊥ p x y (wpq , hip)
      with <M>-elim (sym hip)
    ...| r0 , r1 , r2 = inl≡inr→⊥ (sym r1)

    ⟶-setr-inr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (p : D A t tv)(x : ElU tv t)(y : ElU ty t)
      → (D-setr x y) ⟶ (D-inr p)
      → ⊥
    ⟶-setr-inr-⊥ p x y (wpq , hip)
      with <M>-elim (sym hip)
    ...| r0 , r1 , r2 = inl≡inr→⊥ r1

    ⟶-setl-setl-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (x0 x1 : ElU tv t)(y0 y1 : ElU ty t)
      → (D-setl {A = A} x0 y0) ⟶ (D-setl x1 y1)
      → ⊥
    ⟶-setl-setl-⊥ x0 x1 y0 y1 (wpq , hip)
      = inl≡inr→⊥ (just-inj (sym hip))

    ⟶-setr-setr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      → (x0 x1 : ElU ty t)(y0 y1 : ElU tv t)
      → (D-setr {A = A} x0 y0) ⟶ (D-setr x1 y1)
      → ⊥
    ⟶-setr-setr-⊥ x0 x1 y0 y1 (wpq , hip)
      = inl≡inr→⊥ (just-inj hip)

    ⟶-def : {A : TU→Set}{n : ℕ}{t : T n}{x : U n}{F : U (suc n)}
          → (p q : D A (x ∷ t) F)
          → D-def p ⟶ D-def q
          → p ⟶ q
    ⟶-def p q ((wp , wq) , hip)
      = (D-def-wf p wp , D-def-wf q wq) , <M>-inj inj-red hip

    ⟶-top : {A : TU→Set}{n : ℕ}{t : T n}{x : U n}
          → (p q : D A t x)
          → D-top p ⟶ D-top q
          → p ⟶ q
    ⟶-top p q ((wp , wq) , hip)
      = (D-top-wf p wp , D-top-wf q wq) , <M>-inj inj-top hip

    ⟶-pop : {A : TU→Set}{n : ℕ}{t : T n}{a b : U n}
          → (p q : D A t b)
          → D-pop {a = a} p ⟶ D-pop q
          → p ⟶ q
    ⟶-pop p q ((wp , wq) , hip)
      = (D-pop-wf p wp , D-pop-wf q wq) , <M>-inj inj-pop hip

    ⟶-mu : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
         → (p q : List (Dμ A t ty))
         → (D-mu p) ⟶ (D-mu q)
         → p ⟶μ q
    ⟶-mu p q ((wp , wq) , prf)
      with D-mu-wf p wp | D-mu-wf q wq
    ...| wp' | wq'
      with Dμ-dst p
    ...| nothing = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just sp
      with Dμ-src q
    ...| nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just dq
      rewrite lhead-elim sp (p2 (p2 wp))
            | lhead-elim dq (p1 (p2 wq))
            = (wp' , wq')
            , cong just (cong (λ P → P ∷ []) (just-inj prf))


    ⟶μ-ins-right
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (a : ValU ty t)(ps qs : List (Dμ A t ty))
      → ps ⟶μ (Dμ-ins a ∷ qs)
      → ps ⟶μ qs
    ⟶μ-ins-right a ps qs ((wp , wq) , prf)
      = (wp , (Dμ-ins-wf a qs wq)) , prf

    ⟶μ-del-left
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (a : ValU ty t)(ps qs : List (Dμ A t ty))
      → (Dμ-del a ∷ ps) ⟶μ qs
      → ps ⟶μ qs
    ⟶μ-del-left a ps qs ((wp , wq) , prf)
      = (Dμ-del-wf a ps wp , wq) , prf

    ⟶μ-ins-[]-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (a : ValU ty t)(ps : List (Dμ A t ty))
      → (Dμ-ins a ∷ ps) ⟶μ []
      → ⊥
    ⟶μ-ins-[]-⊥ a ps ((wp , w[]) , prf)
      with Dμ-dst ps
    ...| nothing  = Maybe-⊥ (sym prf)
    ...| just dps
      with ar 0 a ≤?-ℕ length dps
    ...| no  _ = Maybe-⊥ (sym prf)
    ...| yes _
      with lsplit (ar 0 a) dps
    ...| d0 , d1
      with plug 0 a (map pop d0)
    ...| nothing = Maybe-⊥ (sym prf)
    ...| just a' = ∷≡[]→⊥ (just-inj prf)

    ⟶μ-[]-del-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (a : ValU ty t)(ps : List (Dμ A t ty))
      → [] ⟶μ (Dμ-del a ∷ ps)
      → ⊥
    ⟶μ-[]-del-⊥ a ps ((w[] , wp) , prf)
      with Dμ-src ps
    ...| nothing  = Maybe-⊥ prf
    ...| just sps
      with ar 0 a ≤?-ℕ length sps
    ...| no  _ = Maybe-⊥ prf
    ...| yes _
      with lsplit (ar 0 a) sps
    ...| d0 , d1
      with plug 0 a (map pop d0)
    ...| nothing = Maybe-⊥ prf
    ...| just a' = ∷≡[]→⊥ (sym (just-inj prf))

    ⟶μ-dwn-[]-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (a : D A (u1 ∷ t) ty)(ps : List (Dμ A t ty))
      → (Dμ-dwn a ∷ ps) ⟶μ []
      → ⊥
    ⟶μ-dwn-[]-⊥ a ps ((wp , w[]) , prf)
      with D-dst a
    ...| nothing = Maybe-⊥ (sym (p2 (p2 wp)))
    ...| just a' 
      with Dμ-dst ps
    ...| nothing  = Maybe-⊥ (sym (p2 (p2 wp)))
    ...| just dps
      with ar 0 a' ≤?-ℕ length dps
    ...| no  _ = Maybe-⊥ (sym prf)
    ...| yes _
      with lsplit (ar 0 a') dps
    ...| d0 , d1
      with plug 0 a' (map pop d0)
    ...| nothing = Maybe-⊥ (sym prf)
    ...| just _  = ∷≡[]→⊥ (just-inj prf)

    ⟶μ-[]-dwn-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (a : D A (u1 ∷ t) ty)(ps : List (Dμ A t ty))
      → [] ⟶μ (Dμ-dwn a ∷ ps)
      → ⊥
    ⟶μ-[]-dwn-⊥ a ps ((w[] , wp) , prf)
      with D-src a
    ...| nothing = Maybe-⊥ (sym (p1 (p2 wp)))
    ...| just a' 
      with Dμ-src ps
    ...| nothing  = Maybe-⊥ (sym (p1 (p2 wp)))
    ...| just sps
      with ar 0 a' ≤?-ℕ length sps
    ...| no  _ = Maybe-⊥ prf
    ...| yes _
      with lsplit (ar 0 a') sps
    ...| d0 , d1
      with plug 0 a' (map pop d0)
    ...| nothing = Maybe-⊥ prf
    ...| just _  = ∷≡[]→⊥ (sym (just-inj prf))
      

    ⟶μ-ins-del
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (x y : ValU ty t)(ps qs : List (Dμ A t ty))
      → (Dμ-ins x ∷ ps) ⟶μ (Dμ-del y ∷ qs)
      → (x ≡ y) × (ps ⟶μ qs)
    ⟶μ-ins-del x y ps qs ((wp , wq) , prf)
      with Dμ-ins-wf x ps wp | Dμ-del-wf y qs wq
    ...| wp' | wq'
      with Dμ-dst ps | Dμ-src qs
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just dps | nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just dps | just sqs
      with ar 0 x ≤?-ℕ length dps
    ...| no  _ =  ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| yes _
      with ar 0 y ≤?-ℕ length sqs
    ...| no _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| yes _
      with lsplit (ar 0 x) dps | inspect (lsplit (ar 0 x)) dps
    ...| d0 , d1 | [ DPS ]
      with lsplit (ar 0 y) sqs | inspect (lsplit (ar 0 y)) sqs
    ...| s0 , s1 | [ SQS ]
      with plug 0 x (map pop d0) | inspect (plug 0 x) (map pop d0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just x' | [ X ]
      with plug 0 y (map pop s0) | inspect (plug 0 y) (map pop s0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just y' | [ Y ]
      with ∷-inj (just-inj prf)
    ...| prf0 , prf1
      = (trans (sym (plug-spec-fgt 0 x' x (map pop d0) X)) (sym
        (trans (sym (plug-spec-fgt 0 y' y (map pop s0) Y))
               (cong (fgt 0) (sym (inj-mu prf0))))))
      , (wp' , wq')
      , cong just
             (trans (lsplit-elim (ar 0 x) dps DPS) (sym
             (trans (lsplit-elim (ar 0 y) sqs SQS)
             (cong₂ _++_
               (map-inj-inj pop (λ _ _ → inj-pop)
                 (trans (sym (plug-spec-ch 0 y' y (map pop s0) Y)) (sym
                 (trans (sym (plug-spec-ch 0 x' x (map pop d0) X))
                        (cong (ch 0) (inj-mu prf0))))))
               (sym prf1)))))

    ⟶μ-ins-dwn
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (x : ValU ty t)(y : D A (u1 ∷ t) ty)(ps qs : List (Dμ A t ty))
      → (Dμ-ins x ∷ ps) ⟶μ (Dμ-dwn y ∷ qs)
      → D-src y ≡ just x × (ps ⟶μ qs)
    ⟶μ-ins-dwn x y ps qs ((wp , wq) , prf)
      with Dμ-ins-wf x ps wp | Dμ-dwn-wf y qs wq
    ...| wp' | wy' , wq'
      with Dμ-dst ps | Dμ-src qs
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just dps | nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq'))))
    ...| just dps | just sqs
      with D-src y
    ...| nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wy'))))
    ...| just sy
      with ar 0 x ≤?-ℕ length dps
    ...| no  _ =  ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| yes _
      with ar 0 sy ≤?-ℕ length sqs
    ...| no _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| yes _
      with lsplit (ar 0 x) dps | inspect (lsplit (ar 0 x)) dps
    ...| d0 , d1 | [ DPS ]
      with lsplit (ar 0 sy) sqs | inspect (lsplit (ar 0 sy)) sqs
    ...| s0 , s1 | [ SQS ]
      with plug 0 x (map pop d0) | inspect (plug 0 x) (map pop d0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just x' | [ X ]
      with plug 0 sy (map pop s0) | inspect (plug 0 sy) (map pop s0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just y' | [ Y ]
      with ∷-inj (just-inj prf)
    ...| prf0 , prf1
      = (cong just (trans (sym (plug-spec-fgt 0 y' sy (map pop s0) Y)) (sym
                   (trans (sym (plug-spec-fgt 0 x' x (map pop d0) X))
                          (cong (fgt 0) (inj-mu prf0))))))
      , (wp' , wq')
      , cong just
             (trans (lsplit-elim (ar 0 x) dps DPS) (sym
             (trans (lsplit-elim (ar 0 sy) sqs SQS)
             (cong₂ _++_
               (map-inj-inj pop (λ _ _ → inj-pop)
                 (trans (sym (plug-spec-ch 0 y' sy (map pop s0) Y)) (sym
                 (trans (sym (plug-spec-ch 0 x' x (map pop d0) X))
                        (cong (ch 0) (inj-mu prf0))))))
               (sym prf1)))))

    ⟶μ-dwn-dwn
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (x y : D A (u1 ∷ t) ty)(ps qs : List (Dμ A t ty))
      → (Dμ-dwn x ∷ ps) ⟶μ (Dμ-dwn y ∷ qs)
      → (x ⟶ y) × (ps ⟶μ qs)
    ⟶μ-dwn-dwn x y ps qs ((wp , wq) , prf)
      with Dμ-dwn-wf x ps wp | Dμ-dwn-wf y qs wq
    ...| wx' , wp' | wy' , wq'
      with Dμ-dst ps | Dμ-src qs
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp'))))
    ...| just dps | nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq'))))
    ...| just dps | just sqs
      with D-src y
    ...| nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wy'))))
    ...| just sy
      with D-dst x
    ...| nothing = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wx'))))
    ...| just dx
      with ar 0 dx ≤?-ℕ length dps
    ...| no  _ =  ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| yes _
      with ar 0 sy ≤?-ℕ length sqs
    ...| no _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| yes _
      with lsplit (ar 0 dx) dps | inspect (lsplit (ar 0 dx)) dps
    ...| d0 , d1 | [ DPS ]
      with lsplit (ar 0 sy) sqs | inspect (lsplit (ar 0 sy)) sqs
    ...| s0 , s1 | [ SQS ]
      with plug 0 dx (map pop d0) | inspect (plug 0 dx) (map pop d0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just x' | [ X ]
      with plug 0 sy (map pop s0) | inspect (plug 0 sy) (map pop s0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just y' | [ Y ]
      with ∷-inj (just-inj prf)
    ...| prf0 , prf1
      = ((wx' , wy')
        , (cong just (trans (sym (plug-spec-fgt 0 x' dx (map pop d0) X)) (sym
                     (trans (sym (plug-spec-fgt 0 y' sy (map pop s0) Y))
                            (cong (fgt 0) (inj-mu (sym prf0))))))))
      , ((wp' , wq')
        , cong just (trans (lsplit-elim (ar 0 dx) dps DPS) (sym
                    (trans (lsplit-elim (ar 0 sy) sqs SQS)
                    (cong₂ _++_
                      (map-inj-inj pop (λ _ _ → inj-pop)
                        (trans (sym (plug-spec-ch 0 y' sy (map pop s0) Y)) (sym
                        (trans (sym (plug-spec-ch 0 x' dx (map pop d0) X))
                               (cong (ch 0) (inj-mu prf0))))))
                      (sym prf1)))))
          )

    ⟶μ-dwn-del
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (x : D A (u1 ∷ t) ty)(y : ValU ty t)(ps qs : List (Dμ A t ty))
      → (Dμ-dwn x ∷ ps) ⟶μ (Dμ-del y ∷ qs)
      → (WF x) × (D-dst x ≡ just y) × (ps ⟶μ qs)
    ⟶μ-dwn-del x y ps qs ((wp , wq) , prf)
      with Dμ-dwn-wf x ps wp | Dμ-del-wf y qs wq
    ...| wx' , wp' | wq'
      with Dμ-dst ps | Dμ-src qs
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp'))))
    ...| just dps | nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq'))))
    ...| just dps | just sqs
      with D-dst x
    ...| nothing = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wx'))))
    ...| just dx
      with ar 0 dx ≤?-ℕ length dps
    ...| no  _ =  ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| yes _
      with ar 0 y ≤?-ℕ length sqs
    ...| no _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| yes _
      with lsplit (ar 0 dx) dps | inspect (lsplit (ar 0 dx)) dps
    ...| d0 , d1 | [ DPS ]
      with lsplit (ar 0 y) sqs | inspect (lsplit (ar 0 y)) sqs
    ...| s0 , s1 | [ SQS ]
      with plug 0 dx (map pop d0) | inspect (plug 0 dx) (map pop d0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just x' | [ X ]
      with plug 0 y (map pop s0) | inspect (plug 0 y) (map pop s0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just y' | [ Y ]
      with ∷-inj (just-inj prf)
    ...| prf0 , prf1
      = wx' , (cong just (trans (sym (plug-spec-fgt 0 x' dx (map pop d0) X)) (sym
                   (trans (sym (plug-spec-fgt 0 y' y (map pop s0) Y))
                          (cong (fgt 0) (inj-mu (sym prf0)))))))
      , ((wp' , wq')
        , cong just (trans (lsplit-elim (ar 0 dx) dps DPS) (sym
                    (trans (lsplit-elim (ar 0 y) sqs SQS)
                    (cong₂ _++_
                      (map-inj-inj pop (λ _ _ → inj-pop)
                        (trans (sym (plug-spec-ch 0 y' y (map pop s0) Y)) (sym
                        (trans (sym (plug-spec-ch 0 x' dx (map pop d0) X))
                               (cong (ch 0) (inj-mu prf0))))))
                      (sym prf1)))))
          )
\end{code}
