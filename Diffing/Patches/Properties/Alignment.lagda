\begin{code}
open import Prelude
open import Prelude.ListProperties
  using (lsplit-elim; ∷-inj; map-inj-inj; lhead-elim)
open import Diffing.Universe

open import CF.Properties
  using (plug-spec-ch; plug-spec-fgt)

open import Diffing.Patches.D

module Diffing.Patches.Properties.Alignment where
\end{code}

\begin{code}
  infix 30 _||_ _||μ_
  _||_ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
      → (p q : D A t ty)
      → Set
  _||_ {A} {n} {t} {ty} p q
    = Σ (ElU ty t) (λ x → D-src p ≡ just x × D-src q ≡ just x)

  _||μ_ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → (p q : List (Dμ A t ty))
      → Set
  _||μ_ {A} {n} {t} {ty} p q
    = Σ (List (ElU (μ ty) t)) (λ x → Dμ-src p ≡ just x × Dμ-src q ≡ just x)

  ||-refl : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
          → {x : ElU ty t}{p : D A t ty}
          → D-src p ≡ just x → p || p
  ||-refl {x = x} hip = x , hip , hip

  ||-sym : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
       → {p q : D A t ty}
       → p || q → q || p
  ||-sym (el , ps , qs) = el , qs , ps

  ||-trans : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
           → {p q r : D A t ty}
           → p || q → q || r → p || r
  ||-trans (el1 , ps1 , qs1) (el2 , qs2 , rs2)
    = el1 , ps1 , trans rs2 (trans (sym qs2) qs1)

  ||μ-refl : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
          → {x : List (ElU (μ ty) t)}{p : List (Dμ A t ty)}
          → Dμ-src p ≡ just x → p ||μ p
  ||μ-refl {x = x} hip = x , hip , hip

  ||μ-sym : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
       → {p q : List (Dμ A t ty)}
       → p ||μ q → q ||μ p
  ||μ-sym (el , ps , qs) = el , qs , ps

  ||μ-trans : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
           → {p q r : List (Dμ A t ty)}
           → p ||μ q → q ||μ r → p ||μ r
  ||μ-trans (el1 , ps1 , qs1) (el2 , qs2 , rs2)
    = el1 , ps1 , trans rs2 (trans (sym qs2) qs1)
\end{code}

\begin{code}
  ||-inl-elim : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}{p q : D A t ty}
             → D-inl {b = tv} p || D-inl q
             → p || q
  ||-inl-elim (el , ps , qs)
    with <M>-elim ps | <M>-elim qs
  ||-inl-elim (.(inl r0) , ps , qs)
    | r0 , refl , r2 | .r0 , refl , s2
    = r0 , (r2 , s2)

  ||-inr-elim : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}{p q : D A t tv}
             → D-inr {a = ty} p || D-inr q
             → p || q
  ||-inr-elim (el , ps , qs)
    with <M>-elim ps | <M>-elim qs
  ||-inr-elim (.(inr r0) , ps , qs)
    | r0 , refl , r2 | .r0 , refl , s2
    = r0 , (r2 , s2)

  ||-inl-inr-⊥
    : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      {p : D A t ty}{q : D A t tv}
    → D-inl p || D-inr q → ⊥
  ||-inl-inr-⊥ (el , ps , qs)
    with <M>-elim ps | <M>-elim qs
  ...| r0 , r1 , r2 | s0 , s1 , s2
    = inl≡inr→⊥ (trans (sym r1) s1)

  ||-inl-setr-⊥
    : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      {p : D A t ty}{x : ElU ty t}{y : ElU tv t}
    → D-inl p || D-setr y x → ⊥
  ||-inl-setr-⊥ (el , ps , qs)
    with <M>-elim ps
  ...| r0 , r1 , r2 = inl≡inr→⊥ (trans (sym r1) (sym (just-inj qs)))

  ||-inr-setl-⊥
    : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      {p : D A t tv}{x : ElU ty t}{y : ElU tv t}
    → D-inr p || D-setl x y → ⊥
  ||-inr-setl-⊥ (el , ps , qs)
    with <M>-elim ps
  ...| r0 , r1 , r2 = inl≡inr→⊥ (sym (trans (sym r1) (sym (just-inj qs))))

  ||-setl-setr-⊥
    : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      {x a : ElU ty t}{y b : ElU tv t}
    → D-setl {A = A} x y || D-setr b a → ⊥
  ||-setl-setr-⊥ (el , ps , qs)
    = inl≡inr→⊥ (trans (just-inj ps) (sym (just-inj qs)))

  ||-pair-elim
    : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
      {q1 q2 : D A t ty}{r1 r2 : D A t tv}
    → D-pair q1 r1 || D-pair q2 r2
    → q1 || q2 × r1 || r2
  ||-pair-elim {q1 = q1} {q2} {r1} {r2} ((ela , elb) , ps , qs)
    with D-src r1 | D-src q1
  ...| nothing  | _       = ⊥-elim (Maybe-⊥ (sym ps))
  ...| just sr1 | nothing = ⊥-elim (Maybe-⊥ (sym ps))
  ...| just sr1 | just sq1
    with D-src r2 | D-src q2
  ...| nothing  | _       = ⊥-elim (Maybe-⊥ (sym qs))
  ...| just sr2 | nothing = ⊥-elim (Maybe-⊥ (sym qs))
  ...| just sr2 | just sq2
    = (ela , cong just (p1 (inj-, (just-inj ps))) , cong just (p1 (inj-, (just-inj qs))))
    , (elb , cong just (p2 (inj-, (just-inj ps))) , cong just (p2 (inj-, (just-inj qs))))

  ||-def-elim
    : {A : TU→Set}{n : ℕ}{t : T n}{x : U n}{F : U (suc n)}
      {p q : D A (x ∷ t) F}
    → D-def p || D-def q
    → p || q
  ||-def-elim (red el , ps , qs)
    with <M>-elim ps
  ...| .el , refl , x2
    with <M>-elim qs
  ...| .el , refl , y2 = el , x2 , y2

  ||-top-elim
    : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
      {p q : D A t ty}
    → D-top p || D-top q
    → p || q
  ||-top-elim (top el , ps , qs)
    with <M>-elim ps
  ...| .el , refl , x2
    with <M>-elim qs
  ...| .el , refl , y2 = el , x2 , y2

  ||-pop-elim
    : {A : TU→Set}{n : ℕ}{t : T n}{ty a : U n}
      {p q : D A t ty}
    → D-pop {a = a} p || D-pop q
    → p || q
  ||-pop-elim (pop el , ps , qs)
    with <M>-elim ps
  ...| .el , refl , x2
    with <M>-elim qs
  ...| .el , refl , y2 = el , x2 , y2

  ||-mu-elim
    : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      {p q : List (Dμ A t ty)}
    → D-mu p || D-mu q
    → p ||μ q
  ||-mu-elim {p = p} {q = q} (el , ps , qs)
    with Dμ-src p | Dμ-src q
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym ps))
  ...| just sp | nothing = ⊥-elim (Maybe-⊥ (sym qs))
  ...| just sp | just sq
    rewrite lhead-elim sp ps
      = el ∷ [] , refl , cong just (lhead-elim sq qs)

  ||μ-ins-elim
    : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      {a : ValU ty t}{p q : List (Dμ A t ty)}
    → (Dμ-ins a ∷ p) ||μ q
    → p ||μ q
  ||μ-ins-elim (els , ps , qs) = els , ps , qs

  ||μ-ins-ins-elim
    : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      {a b : ValU ty t}{p q : List (Dμ A t ty)}
    → (Dμ-ins a ∷ p) ||μ (Dμ-ins b ∷ q)
    → p ||μ q
  ||μ-ins-ins-elim (els , ps , qs) = els , ps , qs 

  ||μ-dwn-del-elim
    : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      {a : ValU ty t}{x : D A (u1 ∷ t) ty}{p q : List (Dμ A t ty)}
    → (Dμ-dwn x ∷ p) ||μ (Dμ-del a ∷ q)
    → p ||μ q
  ||μ-dwn-del-elim {ty = ty} {a} {x} {p} {q} (el , ps , qs)
    with D-src x | Dμ-src p | Dμ-src q
  ...| nothing | _ | _ = ⊥-elim (Maybe-⊥ (sym ps))
  ...| just sx | nothing | _ = ⊥-elim (Maybe-⊥ (sym ps))
  ...| just sx | just sp | nothing = ⊥-elim (Maybe-⊥ (sym qs))
  ...| just sx | just sp | just sq
    with ar 0 a ≤?-ℕ length sq
  ...| no  _ = ⊥-elim (Maybe-⊥ (sym qs))
  ...| yes _
    with ar 0 sx ≤?-ℕ length sp
  ...| no  _ = ⊥-elim (Maybe-⊥ (sym ps))
  ...| yes _
    with lsplit (ar 0 a) sq | inspect (lsplit (ar 0 a)) sq
  ...| sq0 , sq1 | [ SQ ]
    with lsplit (ar 0 sx) sp | inspect (lsplit (ar 0 sx)) sp
  ...| sp0 , sp1 | [ SP ]
    with plug 0 a (map pop sq0) | inspect (plug 0 a) (map pop sq0)
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym qs))
  ...| just a' | [ A ]
    with plug 0 sx (map pop sp0) | inspect (plug 0 sx) (map pop sp0)
  ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym ps))
  ...| just sx' | [ SX ]
    = sp0 ++ sp1
    , (cong just (lsplit-elim (ar 0 sx) sp SP ))
    , cong just (trans (lsplit-elim (ar 0 a) sq SQ)
                (trans (cong (_++_ sq0) (p2 (∷-inj (just-inj (trans qs (sym ps))))))
                (cong (λ P → P ++ sp1) (map-inj-inj (pop {a = μ ty}) (λ _ _ → inj-pop) {sq0} {sp0}
                      (trans (sym (plug-spec-ch 0 a' a (map pop sq0) A))
                      (sym (trans (sym (plug-spec-ch 0 sx' sx (map pop sp0) SX))
                           (cong (ch 0) (inj-mu (p1 (∷-inj (just-inj (trans ps (sym qs)))))))))))
                 )))

  ||μ-dwn-dwn-elim
    : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      {x y : D A (u1 ∷ t) ty}{p q : List (Dμ A t ty)}
    → (Dμ-dwn x ∷ p) ||μ (Dμ-dwn y ∷ q)
    → p ||μ q × x || y
  ||μ-dwn-dwn-elim {ty = ty} {x} {y} {p} {q} (el , ps , qs)
    with D-src x | Dμ-src p
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym ps))
  ...| just sx | nothing = ⊥-elim (Maybe-⊥ (sym ps))
  ...| just sx | just sp
    with D-src y | Dμ-src q
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym qs))
  ...| just sy | nothing = ⊥-elim (Maybe-⊥ (sym qs))
  ...| just sy | just sq
    with ar 0 sx ≤?-ℕ length sp
  ...| no _ = ⊥-elim (Maybe-⊥ (sym ps))
  ...| yes _
    with ar 0 sy ≤?-ℕ length sq
  ...| no _ = ⊥-elim (Maybe-⊥ (sym qs))
  ...| yes _
    with lsplit (ar 0 sx) sp | inspect (lsplit (ar 0 sx)) sp
  ...| sp0 , sp1 | [ SP ]
    with lsplit (ar 0 sy) sq | inspect (lsplit (ar 0 sy)) sq
  ...| sq0 , sq1 | [ SQ ]
    with plug 0 sx (map pop sp0) | inspect (plug 0 sx) (map pop sp0)
  ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym ps))
  ...| just sx' | [ SX ]
    with plug 0 sy (map pop sq0) | inspect (plug 0 sy) (map pop sq0)
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym qs))
  ...| just sy' | [ SY ]
    = (sp0 ++ sp1
    , cong just (lsplit-elim (ar 0 sx) sp SP)
    , cong just (trans (lsplit-elim (ar 0 sy) sq SQ)
                (trans (cong (_++_ sq0) (p2 (∷-inj (just-inj (trans qs (sym ps))))))
                (cong (λ P → P ++ sp1) (map-inj-inj (pop {a = μ ty}) (λ _ _ → inj-pop) {sq0} {sp0}
                      (trans (sym (plug-spec-ch 0 sy' sy (map pop sq0) SY))
                      (sym (trans (sym (plug-spec-ch 0 sx' sx (map pop sp0) SX))
                           (cong (ch 0) (inj-mu (p1 (∷-inj (just-inj (trans ps (sym qs)))))))))))
                 ))))
    , (sx , refl
          , cong just (trans (sym (plug-spec-fgt 0 sy' sy (map pop sq0) SY))
                 (sym (trans (sym (plug-spec-fgt 0 sx' sx (map pop sp0) SX))
                      (cong (fgt 0) (inj-mu (p1 (∷-inj (just-inj (trans ps (sym qs))))))))))) 
    

  ||μ-del-del-elim
    : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      {a b : ValU ty t}{p q : List (Dμ A t ty)}
    → (Dμ-del b ∷ p) ||μ (Dμ-del a ∷ q)
    → p ||μ q × b ≡ a
  ||μ-del-del-elim {ty = ty} {a} {b} {p} {q} (el , ps , qs)
    with Dμ-src p | Dμ-src q
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym ps))
  ...| just sp | nothing = ⊥-elim (Maybe-⊥ (sym qs))
  ...| just sp | just sq
    with ar 0 a ≤?-ℕ length sq
  ...| no _ = ⊥-elim (Maybe-⊥ (sym qs))
  ...| yes _
    with ar 0 b ≤?-ℕ length sp
  ...| no _ = ⊥-elim (Maybe-⊥ (sym ps))
  ...| yes _
    with lsplit (ar 0 a) sq | inspect (lsplit (ar 0 a)) sq
  ...| sq0 , sq1 | [ SQ ]
    with lsplit (ar 0 b) sp | inspect (lsplit (ar 0 b)) sp
  ...| sp0 , sp1 | [ SP ]
    with plug 0 a (map pop sq0) | inspect (plug 0 a) (map pop sq0)
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym qs))
  ...| just a' | [ A ]
    with plug 0 b (map pop sp0) | inspect (plug 0 b) (map pop sp0)
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym ps))
  ...| just b' | [ B ]
    = (sp0 ++ sp1
    , cong just (lsplit-elim (ar 0 b) sp SP)
    , cong just (trans (lsplit-elim (ar 0 a) sq SQ)
                (trans (cong (_++_ sq0) (p2 (∷-inj (just-inj (trans qs (sym ps))))))
                (cong (λ P → P ++ sp1) (map-inj-inj (pop {a = μ ty}) (λ _ _ → inj-pop) {sq0} {sp0}
                      (trans (sym (plug-spec-ch 0 a' a (map pop sq0) A))
                      (sym (trans (sym (plug-spec-ch 0 b' b (map pop sp0) B))
                           (cong (ch 0) (inj-mu (p1 (∷-inj (just-inj (trans ps (sym qs)))))))))))
                 )))
    ) , trans (sym (plug-spec-fgt 0 b' b (map pop sp0) B))
        (sym (trans (sym (plug-spec-fgt 0 a' a (map pop sq0) A))
             (cong (fgt 0) (inj-mu (p1 (∷-inj (just-inj (trans qs (sym ps)))))))))
\end{code}
