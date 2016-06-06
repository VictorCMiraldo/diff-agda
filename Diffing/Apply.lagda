\begin{code}
open import Prelude
open import Prelude.ListProperties
  using (lhead-elim; map-lemma; lsplit-elim)
open import Diffing.Universe
open import CF.Properties.Base
  using (plug-correct; plug-spec-fgt; plug-spec-ch)
open import CF.Properties.Mu
  using (μ-close-correct; μ-ar-close-lemma; μ-open-ar-lemma)
open import Diffing.Patches.D

module Diffing.Apply where
\end{code}

\begin{code}
  open import Prelude.Monad
  open Monad {{...}}

  _<$>_ : ∀{a b}{A : Set a}{B : Set b} 
        → (A → B) → Maybe A → Maybe B
  _<$>_ = _<M>_

  infixl 20 _<$>_

  pattern True = yes _
  pattern False = no _

  _==_ : {n : ℕ}{t : T n}{ty : U n}(a b : ElU ty t)
       → Dec (a ≡ b)
  _==_ = _≟-U_

  mutual
\end{code}
%<*gapply-type>
\begin{code}
    gapply : {n : ℕ}{t : T n}{ty : U n}
           → Patch t ty → ElU ty t → Maybe (ElU ty t)
\end{code}
%</gapply-type>
\begin{code}
    gapply (D-A ())

    gapply D-unit unit = just unit
\end{code}
%<*gapply-sum-def>
\begin{code}
    gapply (D-inl diff) (inl el) = inl <$> gapply diff el
    gapply (D-inr diff) (inr el) = inr <$> gapply diff el
    gapply (D-setl x y) (inl el) with x ≟-U el
    ...| yes _ = just (inr y)
    ...| no  _ = nothing
    gapply (D-setr y x) (inr el) with y ≟-U el
    ...| yes _ = just (inl x)
    ...| no  _ = nothing
    gapply (D-setr _ _) (inl _) = nothing
    gapply (D-setl _ _) (inr _) = nothing
    gapply (D-inl diff) (inr el) = nothing
    gapply (D-inr diff) (inl el) = nothing
\end{code}
%</gapply-sum-def>
\begin{code}
    gapply (D-pair da db) (a , b) with gapply da a
    ...| nothing = nothing
    ...| just ra = _,_ ra <$> gapply db b

    gapply (D-def diff) (red el) = red <$> gapply diff el
    gapply (D-top diff) (top el) = top <$> gapply diff el
    gapply (D-pop diff) (pop el) = pop <$> gapply diff el
\end{code}
%<*gapply-mu-def>
\begin{code}
    gapply {ty = μ ty} (D-mu d) el = gapplyL d (el ∷ []) >>= lhead
\end{code}
%</gapply-mu-def>

%<*gIns-type>
\begin{code}
    gIns : {n : ℕ}{t : T n}{ty : U (suc n)}
         → ElU ty (u1 ∷ t) → List (ElU (μ ty) t) → Maybe (List (ElU (μ ty) t))
\end{code}
%</gIns-type>
%<*gIns-def>
\begin{code}
    gIns x l with μ-close x l
    ...| nothing = nothing
    ...| just (r , l') = just (r ∷ l')
\end{code}
%</gIns-def>

%<*gDel-type>
\begin{code}
    gDel : {n : ℕ}{t : T n}{ty : U (suc n)}
         → ElU ty (u1 ∷ t) → List (ElU (μ ty) t) → Maybe (List (ElU (μ ty) t))
\end{code}
%</gDel-type>
%<*gDel-def>
\begin{code}
    gDel x [] = nothing
    gDel x (y ∷ ys) with x == (μ-hd y)
    ...| True = just (μ-ch y ++ ys)
    ...| False = nothing
\end{code}
%</gDel-def>

%<*gapplyL-def>
\begin{code}
    gapplyL : {n : ℕ}{t : T n}{ty : U (suc n)}
            → Patchμ t ty → List (ElU (μ ty) t) → Maybe (List (ElU (μ ty) t))
    gapplyL [] [] = just []
    gapplyL [] _  = nothing
    gapplyL (Dμ-A () ∷ _)
    gapplyL (Dμ-ins x  ∷ d) l = gapplyL d l >>= gIns x
    gapplyL (Dμ-del x  ∷ d) l = gDel x l    >>= gapplyL d 
    gapplyL (Dμ-dwn dx ∷ d) [] = nothing
    gapplyL (Dμ-dwn dx ∷ d) (y ∷ l) with μ-open y
    ...| hdY , chY with gapply dx hdY
    ...| nothing = nothing
    ...| just y' = gapplyL d (chY ++ l) >>= gIns y' 
\end{code}
%</gapplyL-def>

  Soundess of apply

\begin{code}
  mutual
    gapplyL-Δ-lemma
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → {xs ys : List (ElU (μ ty) t)}(p : List (Dμ ⊥ₚ t ty))
      → Dμ-Δ p ≡ just (xs , ys)
      → gapplyL p xs ≡ just ys

    gapply-Δ-lemma
      : {n : ℕ}{t : T n}{ty : U n}
      → {x y : ElU ty t}(p : Patch t ty)
      → D-Δ p ≡ just (x , y)
      → gapply p x ≡ just y
    gapply-Δ-lemma (D-A x₁) ()
    gapply-Δ-lemma D-unit refl = refl
    gapply-Δ-lemma (D-inl p) hip
      with <M>-elim hip
    gapply-Δ-lemma {x = .(inl h01)} {.(inl h02)} (D-inl p) hip 
      | (h01 , h02) , refl , h2
      = <M>-intro (gapply-Δ-lemma p h2)
    gapply-Δ-lemma (D-inr p) hip
      with <M>-elim hip
    gapply-Δ-lemma {x = .(inr h01)} {.(inr h02)} (D-inr p) hip 
      | (h01 , h02) , refl , h2
      = <M>-intro (gapply-Δ-lemma p h2)
    gapply-Δ-lemma (D-setl xa xb) refl
      rewrite ≟-U-refl xa = refl
    gapply-Δ-lemma (D-setr xa xb) refl
      rewrite ≟-U-refl xa = refl
    gapply-Δ-lemma (D-def p) hip
      with <M>-elim hip
    ...| r , refl , t = <M>-intro (gapply-Δ-lemma p t)
    gapply-Δ-lemma (D-top p) hip
      with <M>-elim hip
    ...| r , refl , t = <M>-intro (gapply-Δ-lemma p t)
    gapply-Δ-lemma (D-pop p) hip
      with <M>-elim hip
    ...| r , refl , t = <M>-intro (gapply-Δ-lemma p t)
    gapply-Δ-lemma (D-pair p p₁) hip
      with <M*>-elim-full {x = D-Δ p₁} hip
    ...| (f , (a0 , a1)) , (b0 , refl , b2) with <M>-elim b0
    ...| (r0 , r1) , s , t
      rewrite s
        | gapply-Δ-lemma p t
        | gapply-Δ-lemma p₁ b2
        = refl
    gapply-Δ-lemma (D-mu x) hip
      with Dμ-Δ x | inspect Dμ-Δ x
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just (sx , dx) | [ X ]
      with <M*>-elim-full {x = lhead dx} hip
    ...| (f , a) , (s0 , s1 , s2)
      with <M>-elim s0
    ...| r0 , r1 , r2
      rewrite r1 | p1 (×-inj s1) | p2 (×-inj s1)
        | lhead-elim sx r2
        | lhead-elim dx s2
        | gapplyL-Δ-lemma x X
        = refl
      
    gapplyL-Δ-lemma [] refl = refl
    gapplyL-Δ-lemma (Dμ-A () ∷ p) hip
    gapplyL-Δ-lemma (Dμ-ins x ∷ p) hip
      with Dμ-Δ p | inspect Dμ-Δ p
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just (sp , dp) | [ SP ] with <M>-elim hip
    ...| r , refl , t rewrite gapplyL-Δ-lemma p SP
      with ar 0 x ≤?-ℕ length dp
    ...| no  _   = ⊥-elim (Maybe-⊥ (sym hip))
    ...| yes prf with lsplit (ar 0 x) dp
    ...| dp0 , dp1 with plug 0 x (map pop dp0)
    ...| nothing = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just x' = t
    gapplyL-Δ-lemma (Dμ-del x ∷ p) hip
      with Dμ-Δ p | inspect Dμ-Δ p
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just (sp , dp) | [ SP ] with <M>-elim hip
    ...| r , refl , t with ar 0 x ≤?-ℕ length sp
    ...| no  _   = ⊥-elim (Maybe-⊥ (sym hip))
    ...| yes prf with lsplit (ar 0 x) sp | inspect (lsplit (ar 0 x)) sp
    ...| sp0 , sp1 | [ SP-split ]
      with plug 0 x (map pop sp0) | inspect (plug 0 x) (map pop sp0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just x' | [ X ]
      rewrite sym (just-inj t)
      with x == fgt 0 x'
    ...| no  abs = ⊥-elim (abs (sym (plug-spec-fgt 0 x' x (map pop sp0) X)))
    ...| yes _ rewrite plug-spec-ch 0 x' x (map pop sp0) X
       = trans (cong (λ P → gapplyL p (P ++ sp1)) (map-lemma sp0 (λ _ → refl)))
        (trans (cong (gapplyL p) (sym (lsplit-elim (ar 0 x) sp SP-split)))
               (gapplyL-Δ-lemma p SP))
    gapplyL-Δ-lemma {ty = ty} (Dμ-dwn x ∷ p) hip
      with D-Δ x | inspect D-Δ x | Dμ-Δ p | inspect Dμ-Δ p
    ...| nothing | _ | _ | _ = ⊥-elim (Maybe-⊥ (sym hip))
    ...| just _  | _ | nothing | _ = ⊥-elim (Maybe-⊥ (sym hip)) 
    ...| just (sx , dx) | [ DX ] | just (sp , dp) | [ DXS ]
      with <M*>-elim-full {x = μ-close dx dp >>= (return ∘ cons)} hip
    ...| (f , a) , (s0 , s1 , s2) with <M>-elim s0
    ...| r0 , r1 , r2 
      with ar 0 sx ≤?-ℕ length sp
    ...| no  _    = ⊥-elim (Maybe-⊥ (sym r2))
    ...| yes arp1
      with ar 0 dx ≤?-ℕ length dp
    ...| no  _    = ⊥-elim (Maybe-⊥ (sym s2))
    ...| yes arp2
      with lsplit (ar 0 sx) sp | inspect (lsplit (ar 0 sx)) sp
    ...| sp0 , sp1 | [ SP ]
      with lsplit (ar 0 dx) dp | inspect (lsplit (ar 0 dx)) dp
    ...| dp0 , dp1 | [ DP ]
      rewrite r1 | p1 (×-inj s1) | p2 (×-inj s1)
      with plug 0 dx (map pop dp0) | inspect (plug 0 dx) (map pop dp0)
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym s2))
    ...| just dx' | [ PDX ]
      with plug 0 sx (map pop sp0) | inspect (plug 0 sx) (map pop sp0)
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym r2))
    ...| just sx' | [ PSX ]
      rewrite p1 (×-inj (just-inj (sym hip)))
            | p2 (×-inj (just-inj (sym hip)))
            | plug-spec-fgt 0 sx' sx (map pop sp0) PSX
            | gapply-Δ-lemma x DX
            | plug-spec-ch 0 sx' sx (map pop sp0) PSX
            | map-lemma {f = pop {a = μ ty}} {g = unpop} sp0 (λ _ → refl)
            | sym (lsplit-elim (ar 0 sx) sp SP)
            | gapplyL-Δ-lemma p DXS
       with ar 0 dx ≤?-ℕ length dp
    ...| no  abs = ⊥-elim (abs arp2)
    ...| yes _ rewrite DP | PDX
       = refl
\end{code}
