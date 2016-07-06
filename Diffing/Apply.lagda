\begin{code}
open import Prelude
open import Prelude.ListProperties
  using (lhead-elim; map-lemma; lsplit-elim; ∷≡[]→⊥; ∷-inj)
open import Prelude.NatProperties
  using (≤-yes)
open import Diffing.Universe
open import CF.Properties.Base
  using (plug-correct; plug-spec-fgt; plug-spec-ch)
open import CF.Properties.Mu
  using (μ-close-correct; μ-ar-close-lemma; μ-open-ar-lemma)
open import Diffing.Patches.D
open import Diffing.Patches.Properties.WellFormed

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
    gapply-spec
      : {n : ℕ}{t : T n}{ty : U n}
      → (p : Patch t ty)(hip : WF p)
      → gapply p (D-src-wf (p , hip)) ≡ just (D-dst-wf (p , hip))

    gapplyL-spec
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (ps : Patchμ t ty)(hip : WFμ ps)
      → gapplyL ps (Dμ-src-wf (ps , hip)) ≡ just (Dμ-dst-wf (ps , hip))

    gapply-spec (D-A ()) hip
    gapply-spec D-unit ((.unit , .unit) , refl , refl) = refl
    gapply-spec (D-inl p) hip
      with <M>-elim (p1 (p2 hip)) | <M>-elim (p2 (p2 hip))
    ...| r0 , r1 , r2 | s0 , s1 , s2
      rewrite r1 | s1 = <M>-intro (gapply-spec p ((r0 , s0) , (r2 , s2)))
    gapply-spec (D-inr p) hip
      with <M>-elim (p1 (p2 hip)) | <M>-elim (p2 (p2 hip))
    ...| r0 , r1 , r2 | s0 , s1 , s2
      rewrite r1 | s1 = <M>-intro (gapply-spec p ((r0 , s0) , (r2 , s2)))
    gapply-spec (D-setl xa xb) ((.(inl xa) , .(inr xb)) , refl , refl)
      rewrite ≟-U-refl xa = refl
    gapply-spec (D-setr xa xb) ((.(inr xa) , .(inl xb)) , refl , refl)
      rewrite ≟-U-refl xa = refl 
    gapply-spec (D-def p) hip
      with <M>-elim (p1 (p2 hip)) | <M>-elim (p2 (p2 hip))
    ...| r0 , r1 , r2 | s0 , s1 , s2
      rewrite r1 | s1 = <M>-intro (gapply-spec p ((r0 , s0) , (r2 , s2)))
    gapply-spec (D-top p) hip
      with <M>-elim (p1 (p2 hip)) | <M>-elim (p2 (p2 hip))
    ...| r0 , r1 , r2 | s0 , s1 , s2
      rewrite r1 | s1 = <M>-intro (gapply-spec p ((r0 , s0) , (r2 , s2)))
    gapply-spec (D-pop p) hip
      with <M>-elim (p1 (p2 hip)) | <M>-elim (p2 (p2 hip))
    ...| r0 , r1 , r2 | s0 , s1 , s2
      rewrite r1 | s1 = <M>-intro (gapply-spec p ((r0 , s0) , (r2 , s2)))
    gapply-spec (D-pair p q) (((x1 , x2) , (y1 , y2)) , (hx , hy))
      with <M*>-elim-full {x = D-dst q} hy
    ...| (f0 , a0) , (r0 , r1 , r2)
      with <M*>-elim-full {x = D-src q} hx
    ...| (f1 , a1) , (s0 , s1 , s2)
      with <M>-elim r0 | <M>-elim s0
    ...| k0 , k1 , k2 | l0 , l1 , l2
      rewrite l1 | k1 | p1 (inj-, s1) | p2 (inj-, s1)
            | p1 (inj-, r1) | p2 (inj-, r1)
            | gapply-spec p ((l0 , k0) , (l2 , k2))
            | gapply-spec q ((a1 , a0) , (s2 , r2))
            = refl
    gapply-spec (D-mu x) ((sx , dx) , (hsx , hdx))
      with Dμ-src x | inspect Dμ-src x
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hsx))
    ...| just ssx | [ SSX ]
      with Dμ-dst x | inspect Dμ-dst x
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hdx))
    ...| just ddx | [ DDX ]
      rewrite lhead-elim ssx hsx
            | lhead-elim ddx hdx
            | gapplyL-spec x ((sx ∷ [] , dx ∷ []) , SSX , DDX)
            = refl

    gapplyL-spec [] ((.[] , .[]) , refl , refl) = refl
    gapplyL-spec (Dμ-A () ∷ ps) hip
    gapplyL-spec (Dμ-ins p ∷ ps) ((x , y) , (hx , hy))
      with Dμ-dst ps | inspect Dμ-dst ps
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym hy))
    ...| just dst | [ PS ]
      rewrite gapplyL-spec ps ((x , dst) , (hx , PS))
      with ar 0 p ≤?-ℕ length dst
    ...| no  _ = ⊥-elim (Maybe-⊥ (sym hy))
    ...| yes _
      with lsplit (ar 0 p) dst | inspect (lsplit (ar 0 p)) dst
    ...| d0 , d1 | [ DST ]
      with plug 0 p (map pop d0)
    ...| nothing = ⊥-elim (Maybe-⊥ (sym hy))
    ...| just p' = hy
    gapplyL-spec (Dμ-del p ∷ ps) ((x , y) , (hx , hy))
      with Dμ-src ps | inspect Dμ-src ps
    ...| nothing  | _ = ⊥-elim (Maybe-⊥ (sym hx))
    ...| just src | [ PS ]
      with ar 0 p ≤?-ℕ length src
    ...| no  _ = ⊥-elim (Maybe-⊥ (sym hx))
    ...| yes _
      with lsplit (ar 0 p) src | inspect (lsplit (ar 0 p)) src
    ...| s0 , s1 | [ SRC ]
      with plug 0 p (map pop s0) | inspect (plug 0 p) (map pop s0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hx))
    ...| just p' | [ P ]
      with x
    ...| [] = ⊥-elim (∷≡[]→⊥ (just-inj hx))
    ...| (mu z ∷ zs)
      with p == μ-hd (mu z)
    ...| no abs = ⊥-elim (abs (trans (sym (plug-spec-fgt 0 p' p (map pop s0) P))
                                     (cong (fgt 0) (inj-mu (p1 (∷-inj (just-inj hx)))))))
    ...| yes _
       = gapplyL-spec ps
         ((map unpop (ch 0 z) ++ zs , y)
         , (trans PS (cong just (trans (lsplit-elim (ar 0 p) src SRC)
                     (cong₂ _++_ (sym (trans (cong (λ Q → map unpop (ch 0 Q))
                                                   (sym (inj-mu (p1 (∷-inj (just-inj hx))))))
                                             (trans (cong (map unpop)
                                                          (plug-spec-ch 0 p' p (map pop s0) P))
                                                    (map-lemma s0 (λ _ → refl)))))
                                 (p2 (∷-inj (just-inj hx)))))))
                  , hy)
    gapplyL-spec (Dμ-dwn p ∷ ps) ((x , y) , (hx , hy))
      with D-src p | inspect D-src p | D-dst p | inspect D-dst p
    ...| nothing | _ | _ | _ = ⊥-elim (Maybe-⊥ (sym hx))
    ...| just sp | _ | nothing | _ = ⊥-elim (Maybe-⊥ (sym hy))
    ...| just sp | [ SRCP ] | just dp | [ DSTP ] 
      with Dμ-src ps | inspect Dμ-src ps | Dμ-dst ps | inspect Dμ-dst ps
    ...| nothing | _ | _ | _ = ⊥-elim (Maybe-⊥ (sym hx))
    ...| just sps | _ | nothing | _ = ⊥-elim (Maybe-⊥ (sym hy))
    ...| just sps | [ SRCPS ] | just dps | [ DSTPS ]
      with ar 0 dp ≤?-ℕ length dps
    ...| no  _ = ⊥-elim (Maybe-⊥ (sym hy))
    ...| yes dp≤dps
      with ar 0 sp ≤?-ℕ length sps
    ...| no  _ = ⊥-elim (Maybe-⊥ (sym hx))
    ...| yes _
      with lsplit (ar 0 sp) sps | inspect (lsplit (ar 0 sp)) sps
    ...| sps0 , sps1 | [ SPS ]
      with lsplit (ar 0 dp) dps | inspect (lsplit (ar 0 dp)) dps
    ...| dps0 , dps1 | [ DPS ]
      with plug 0 dp (map pop dps0) | inspect (plug 0 dp) (map pop dps0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hy))
    ...| just dp' | [ DP ]
      with plug 0 sp (map pop sps0) | inspect (plug 0 sp) (map pop sps0)
    ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hx))
    ...| just sp' | [ SP ]
      rewrite just-inj (sym hx)
            | just-inj (sym hy)
            | plug-spec-fgt 0 sp' sp (map pop sps0) SP
            | gapply-spec p ((sp , dp) , SRCP , DSTP)
            | gapplyL-spec ps ((map unpop (ch 0 sp') ++ sps1 , dps)
                , trans (trans SRCPS (cong just (lsplit-elim (ar 0 sp) sps SPS)))
                  ( (cong (λ Q → just (Q ++ sps1))
                        (sym (trans (cong (map unpop) (plug-spec-ch 0 sp' sp (map pop sps0) SP))
                             (map-lemma sps0 (λ _ → refl))))) )
                , DSTPS
                )
            | ≤-yes dp≤dps
            | DPS
            | DP
            = refl
\end{code}
