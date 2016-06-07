\begin{code}
open import Prelude
open import Prelude.ListProperties
  using (lsplit-elim; ∷-inj; map-inj-inj; lhead-elim)
open import Diffing.Universe

open import CF.Properties
  using (plug-spec-ch; plug-spec-fgt)

open import Diffing.Patches.D
open import Diffing.Patches.Properties.WellFounded

module Diffing.Patches.Properties.Alignment where
\end{code}

\begin{code}
  infix 30 _||_ _||μ_

  abstract
    _||_ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
        → (p q : D A t ty)
        → Set
    _||_ {A} {n} {t} {ty} p q
      = (WF p × WF q) × D-src p ≡ D-src q

    _||μ_ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
        → (p q : List (Dμ A t ty))
        → Set
    _||μ_ {A} {n} {t} {ty} p q
      = (WFμ p × WFμ q) × Dμ-src p ≡ Dμ-src q
\end{code}

\begin{code}
    ||-elim : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
            → {p q : D A t ty}
            → p || q
            → (WF p × WF q) × D-src p ≡ D-src q
    ||-elim hip = hip
          
    ||-intro : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
            → {p q : D A t ty}
            → (WF p × WF q) × D-src p ≡ D-src q
            → p || q
    ||-intro hip = hip

    ||μ-elim : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
             → {p q : List (Dμ A t ty)}
             → p ||μ q
             → (WFμ p × WFμ q) × Dμ-src p ≡ Dμ-src q
    ||μ-elim hip = hip

    ||μ-intro : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
              → {p q : List (Dμ A t ty)}
              → (WFμ p × WFμ q) × Dμ-src p ≡ Dμ-src q
              → p ||μ q
    ||μ-intro hip = hip
\end{code}

\begin{code}
    ||-refl : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
            → {x : ElU ty t}(p : D A t ty)
            → WF p → p || p
    ||-refl p hip = (hip , hip) , refl

    ||-sym : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
           → {p q : D A t ty}
           → p || q → q || p
    ||-sym ((wp , wq) , prf) = (wq , wp) , sym prf

    ||-trans : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
             → (p q r : D A t ty)
             → p || q → q || r → p || r
    ||-trans p q r ((wp , wq) , prf1) ((_ , wr) , prf2)
      = (wp , wr) , trans prf1 prf2

    ||μ-refl : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
              → {x : List (ElU (μ ty) t)}(p : List (Dμ A t ty))
              → WFμ p → p ||μ p
    ||μ-refl p hip = (hip , hip) , refl

    ||μ-sym : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
            → {p q : List (Dμ A t ty)}
            → p ||μ q → q ||μ p
    ||μ-sym  ((wp , wq) , prf) = (wq , wp) , sym prf

    ||μ-trans : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
             → (p q r : List (Dμ A t ty))
             → p ||μ q → q ||μ r → p ||μ r
    ||μ-trans p q r ((wp , wq) , prf1) ((_ , wr) , prf2)
      = (wp , wr) , trans prf1 prf2
\end{code}

\begin{code}
    ||-inl-elim : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
                → (p q : D A t ty)
                → D-inl {b = tv} p || D-inl q
                → p || q
    ||-inl-elim p q ((wp , wq) , prf)
      = (D-inl-wf p wp , D-inl-wf q wq) , <M>-inj inj-inl prf


    ||-inr-elim : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
                → (p q : D A t tv)
                → D-inr {a = ty} p || D-inr q
                → p || q
    ||-inr-elim p q ((wp , wq) , prf)
      = (D-inr-wf p wp , D-inr-wf q wq) , <M>-inj inj-inr prf


    ||-inl-inr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
        (p : D A t ty)(q : D A t tv)
      → D-inl p || D-inr q → ⊥
    ||-inl-inr-⊥ p q ((((sp , dp) , (hsp , hdp)) , ((sq , dq) , (hsq , hdq))) , prf)
      with <M>-elim hsq | <M>-elim hsp
    ...| r0 , r1 , r2 | s0 , s1 , s2
      rewrite r2 | s2 = inl≡inr→⊥ (just-inj prf)

    ||-inl-setr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
        (p : D A t ty)(x : ElU ty t)(y : ElU tv t)
      → D-inl p || D-setr y x → ⊥
    ||-inl-setr-⊥ p x y ((wp , wq) , prf)
      with <M>-elim prf
    ...| r0 , r1 , r2 = inl≡inr→⊥ (sym r1)

    ||-inr-setl-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
        (p : D A t tv)(x : ElU ty t)(y : ElU tv t)
      → D-inr p || D-setl x y → ⊥
    ||-inr-setl-⊥ p x y ((wp , wq) , prf)
      with <M>-elim prf
    ...| r0 , r1 , r2 = inl≡inr→⊥ r1

    ||-setl-setr-⊥
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
        (x a : ElU ty t)(y b : ElU tv t)
      → D-setl {A = A} x y || D-setr b a → ⊥
    ||-setl-setr-⊥ x a y b ((wp , wq) , prf)
      = inl≡inr→⊥ (just-inj prf)


    ||-pair-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
        (q1 q2 : D A t ty)(r1 r2 : D A t tv)
      → D-pair q1 r1 || D-pair q2 r2
      → q1 || q2 × r1 || r2
    ||-pair-elim q1 q2 r1 r2
      ((((sdq0 , sdq1) , wq1 , wr1) , ((sdr0 , sdr1) , wq2 , wr2)) , prf)
      with <M*>-elim-full {x = D-dst r2} wr2
    ...| (f0 , a0) , (t0 , x0 , v0)
      with <M*>-elim-full {x = D-src r2} wq2
    ...| (f1 , a1) , (t1 , x1 , v1)
      with <M*>-elim-full {x = D-dst r1} wr1
    ...| (f2 , a2) , (t2 , x2 , v2)
      with <M*>-elim-full {x = D-src r1} wq1
    ...| (f3 , a3) , (t3 , x3 , v3)
      with <M>-elim t0 | <M>-elim t1
    ...| b0 , b1 , b2 | c0 , c1 , c2
      with <M>-elim t2 | <M>-elim t3
    ...| d0 , d1 , d2 | e0 , e1 , e2
      rewrite v0 | v1 | v2 | v3 | b2 | c2 | d2 | e2
      = ((((e0 , d0) , refl , refl) , ((c0 , b0) , refl , refl))
              , cong just (p1 (inj-, (just-inj prf))))
      , ((((a3 , a2) , refl , refl) , ((a1 , a0) , refl , refl))
              , cong just (p2 (inj-, (just-inj prf))))

    ||-def-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{x : U n}{F : U (suc n)}
      → (p q : D A (x ∷ t) F)
      → D-def p || D-def q
      → p || q
    ||-def-elim p q ((wp , wq) , prf)
      = (D-def-wf p wp , D-def-wf q wq) , <M>-inj inj-red prf

    ||-top-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
      → (p q : D A t ty)
      → D-top p || D-top q
      → p || q
    ||-top-elim p q ((wp , wq) , prf)
      = (D-top-wf p wp , D-top-wf q wq) , <M>-inj inj-top prf

    ||-pop-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty a : U n}
      → (p q : D A t ty)
      → D-pop {a = a} p || D-pop q
      → p || q
    ||-pop-elim p q ((wp , wq) , prf)
      = (D-pop-wf p wp , D-pop-wf q wq) , <M>-inj inj-pop prf

    ||-mu-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
        (p q : List (Dμ A t ty))
      → D-mu p || D-mu q
      → p ||μ q
    ||-mu-elim p q ((wp , wq) , prf)
      with Dμ-src p | Dμ-src q
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| just sp | nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just sp | just sq
      with Dμ-dst p | Dμ-dst q
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just dp | nothing = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wq))))
    ...| just dp | just dq  
      rewrite lhead-elim sp (p1 (p2 wp))
            | lhead-elim sq (p1 (p2 wq))
            = (((p1 (p1 wp) ∷ [] , dp) , refl , refl)
            , (((p1 (p1 wq) ∷ []) , dq) , refl , refl))
            , (cong (λ P → just (P ∷ [])) (just-inj prf))

    ||μ-ins-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
        (a : ValU ty t)(p q : List (Dμ A t ty))
      → (Dμ-ins a ∷ p) ||μ q
      → p ||μ q
    ||μ-ins-elim a p q ((wp , wq) , prf)
      = (Dμ-ins-wf a p wp , wq) , prf

    ||μ-ins-ins-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
        (a b : ValU ty t)(p q : List (Dμ A t ty))
      → (Dμ-ins a ∷ p) ||μ (Dμ-ins b ∷ q)
      → p ||μ q
    ||μ-ins-ins-elim a b p q ((wp , wq) , prf)
      = (Dμ-ins-wf a p wp , Dμ-ins-wf b q wq) , prf

    ||μ-dwn-del-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
        (a : ValU ty t)(x : D A (u1 ∷ t) ty)(p q : List (Dμ A t ty))
      → (Dμ-dwn x ∷ p) ||μ (Dμ-del a ∷ q)
      → p ||μ q
    ||μ-dwn-del-elim {ty = ty} a x p q ((wp , wq) , prf)
      with D-src x | Dμ-src p | Dμ-src q
    ...| nothing | _ | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| just sx | nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| just sx | just sp | nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just sx | just sp | just sq
      with D-dst x | Dμ-dst p | Dμ-dst q
    ...| nothing | _ | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just dx | nothing | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just dx | just dp | nothing = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wq))))
    ...| just dx | just dp | just dq
      with ar 0 a ≤?-ℕ length sq
    ...| no  _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| yes _
      with ar 0 sx ≤?-ℕ length sp
    ...| no  _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| yes _
      with lsplit (ar 0 a) sq | inspect (lsplit (ar 0 a)) sq
    ...| sq0 , sq1 | [ SQ ]
      with lsplit (ar 0 sx) sp | inspect (lsplit (ar 0 sx)) sp
    ...| sp0 , sp1 | [ SP ]
      with plug 0 a (map pop sq0) | inspect (plug 0 a) (map pop sq0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just a' | [ A ]
      with plug 0 sx (map pop sp0) | inspect (plug 0 sx) (map pop sp0)
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| just sx' | [ SX ]
      = (((sp , dp) , refl , refl) , ((sq , dq) , (refl , refl)))
      , cong just
          (trans (lsplit-elim (ar 0 sx) sp SP) (sym
          (trans (lsplit-elim (ar 0 a) sq SQ)
          (trans (cong (λ P → sq0 ++ P) (sym (p2 (∷-inj (just-inj prf)))))
          (cong (λ P → P ++ sp1)
            (map-inj-inj (pop {a = μ ty}) (λ _ _ → inj-pop) {sq0} {sp0}
              ((trans (sym (plug-spec-ch 0 a' a (map pop sq0) A))
                        (sym (trans (sym (plug-spec-ch 0 sx' sx (map pop sp0) SX))
                             (cong (ch 0) (inj-mu (p1 (∷-inj (just-inj prf)))))))))))))))
        

    ||μ-dwn-dwn-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
        (x y : D A (u1 ∷ t) ty)(p q : List (Dμ A t ty))
      → (Dμ-dwn x ∷ p) ||μ (Dμ-dwn y ∷ q)
      → p ||μ q × x || y
    ||μ-dwn-dwn-elim {ty = ty} x y p q ((wp , wq) , prf)
      with D-src x | Dμ-src p
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| just sx | nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| just sx | just sp
      with D-src y | Dμ-src q
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just sy | nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just sy | just sq
      with D-dst x | Dμ-dst p
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just dx | nothing = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just dx | just dp
      with D-dst y | Dμ-dst q
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wq))))
    ...| just dy | nothing = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wq))))
    ...| just dy | just dq
      with ar 0 sx ≤?-ℕ length sp
    ...| no _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| yes _
      with ar 0 sy ≤?-ℕ length sq
    ...| no _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| yes _
      with lsplit (ar 0 sx) sp | inspect (lsplit (ar 0 sx)) sp
    ...| sp0 , sp1 | [ SP ]
      with lsplit (ar 0 sy) sq | inspect (lsplit (ar 0 sy)) sq
    ...| sq0 , sq1 | [ SQ ]
      with plug 0 sx (map pop sp0) | inspect (plug 0 sx) (map pop sp0)
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| just sx' | [ SX ]
      with plug 0 sy (map pop sq0) | inspect (plug 0 sy) (map pop sq0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just sy' | [ SY ]
      = ((((sp , dp) , refl , refl) , ((sq , dq) , refl , refl))
        , cong just
            (trans (lsplit-elim (ar 0 sx) sp SP) (sym
            (trans (lsplit-elim (ar 0 sy) sq SQ)
            (trans (cong (λ P → sq0 ++ P) (sym (p2 (∷-inj (just-inj prf)))))
            (cong (λ P → P ++ sp1)
              (map-inj-inj (pop {a = μ ty}) (λ _ _ → inj-pop) {sq0} {sp0}
                ((trans (sym (plug-spec-ch 0 sy' sy (map pop sq0) SY))
                          (sym (trans (sym (plug-spec-ch 0 sx' sx (map pop sp0) SX))
                               (cong (ch 0) (inj-mu (p1 (∷-inj (just-inj prf))))))))))))))))
      , ((((sx , dx) , refl , refl) , ((sy , dy) , refl , refl))
        , cong just
            (trans (sym (plug-spec-fgt 0 sx' sx (map pop sp0) SX)) (sym
            (trans (sym (plug-spec-fgt 0 sy' sy (map pop sq0) SY))
                   (cong (fgt 0) (inj-mu (p1 (∷-inj (just-inj (sym prf))))))))))

    ||μ-del-del-elim
      : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
        (a b : ValU ty t)(p q : List (Dμ A t ty))
      → (Dμ-del b ∷ p) ||μ (Dμ-del a ∷ q)
      → p ||μ q × b ≡ a
    ||μ-del-del-elim {ty = ty} a b p q ((wp , wq) , prf)
      with Dμ-src p | Dμ-src q
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| just sp | nothing = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just sp | just sq
      with Dμ-dst p | Dμ-dst q
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wp))))
    ...| just dp | nothing = ⊥-elim (Maybe-⊥ (sym (p2 (p2 wq))))
    ...| just dp | just dq
      with ar 0 a ≤?-ℕ length sq
    ...| no _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| yes _
      with ar 0 b ≤?-ℕ length sp
    ...| no _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| yes _
      with lsplit (ar 0 a) sq | inspect (lsplit (ar 0 a)) sq
    ...| sq0 , sq1 | [ SQ ]
      with lsplit (ar 0 b) sp | inspect (lsplit (ar 0 b)) sp
    ...| sp0 , sp1 | [ SP ]
      with plug 0 a (map pop sq0) | inspect (plug 0 a) (map pop sq0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wq))))
    ...| just a' | [ A ]
      with plug 0 b (map pop sp0) | inspect (plug 0 b) (map pop sp0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym (p1 (p2 wp))))
    ...| just b' | [ B ]
      = ((((sp , dp) , refl , refl) , ((sq , dq) , refl , refl))
        , cong just
            (trans (lsplit-elim (ar 0 b) sp SP) (sym
            (trans (lsplit-elim (ar 0 a) sq SQ)
            (trans (cong (λ P → sq0 ++ P) (sym (p2 (∷-inj (just-inj prf)))))
            (cong (λ P → P ++ sp1)
              (map-inj-inj (pop {a = μ ty}) (λ _ _ → inj-pop) {sq0} {sp0}
                ((trans (sym (plug-spec-ch 0 a' a (map pop sq0) A))
                          (sym (trans (sym (plug-spec-ch 0 b' b (map pop sp0) B))
                               (cong (ch 0) (inj-mu (p1 (∷-inj (just-inj prf))))))))))))))))
      , trans (sym (plug-spec-fgt 0 b' b (map pop sp0) B))
          (sym (trans (sym (plug-spec-fgt 0 a' a (map pop sq0) A))
               (cong (fgt 0) (inj-mu (p1 (∷-inj (just-inj (sym prf))))))))
\end{code}
