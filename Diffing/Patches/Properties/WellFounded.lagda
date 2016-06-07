\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Patches.D

module Diffing.Patches.Properties.WellFounded where
\end{code}

%<*WF-def>
\begin{code}
  WF : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
     → D A t ty → Set
  WF {A} {n} {t} {ty} p
    = Σ (ElU ty t × ElU ty t)
        (λ xy → D-src p ≡ just (p1 xy) × D-dst p ≡ just (p2 xy))

  WFμ : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
      → List (Dμ A t ty) → Set
  WFμ {A} {n} {t} {ty} ps
    = Σ (List (ElU (μ ty) t) × List (ElU (μ ty) t))
        (λ xy → Dμ-src ps ≡ just (p1 xy) × Dμ-dst ps ≡ just (p2 xy))
\end{code}
%</WF-def>


%<*D-inl-wf-type>
\begin{code}
  D-inl-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
           → (p : D A t ty)
           → WF (D-inl {b = tv} p)
           → WF p
\end{code}
%</D-inl-wf-type>
%<*D-inl-wf-def>
\begin{code}
  D-inl-wf p ((x , y) , (hx , hy))
    with <M>-elim hx | <M>-elim hy
  ...| r0 , r1 , r2 | s0 , s1 , s2
    = (r0 , s0) , r2 , s2
\end{code}
%</D-inl-wf-def>
\begin{code}
  D-inr-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
           → (p : D A t tv)
           → WF (D-inr {a = ty} p)
           → WF p
  D-inr-wf p ((x , y) , (hx , hy))
    with <M>-elim hx | <M>-elim hy
  ...| r0 , r1 , r2 | s0 , s1 , s2
    = (r0 , s0) , r2 , s2

  D-unit-wf : {A : TU→Set}{n : ℕ}{t : T n}
            → WF {A = A} {n = n} {t = t} D-unit
  D-unit-wf = (unit , unit) , (refl , refl)

  D-setl-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
            → (x : ElU ty t)(y : ElU tv t)
            → WF {A = A} (D-setl x y)
  D-setl-wf x y = (inl x , inr y) , refl , refl

  D-setr-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
            → (x : ElU tv t)(y : ElU ty t)
            → WF {A = A} (D-setr x y)
  D-setr-wf x y = (inr x , inl y) , (refl , refl)

  D-pair-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
            → (p : D A t ty)(q : D A t tv)
            → WF (D-pair p q)
            → WF p × WF q
  D-pair-wf p q ((x , y) , (hx , hy))
    with <M*>-elim-full {x = D-dst q} hy
  ...| (f0 , a0) , (r0 , r1 , r2)
    with <M*>-elim-full {x = D-src q} hx
  ...| (f1 , a1) , (s0 , s1 , s2)
    with <M>-elim r0 | <M>-elim s0
  ...| k0 , k1 , k2 | l0 , l1 , l2
    = ((l0 , k0) , (l2 , k2)) , (a1 , a0) , s2 , r2

  D-top-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
           → (p : D A t ty)
           → WF (D-top p)
           → WF p
  D-top-wf p ((x , y) , (hx , hy))
    with <M>-elim hx | <M>-elim hy
  ...| r0 , r1 , r2 | s0 , s1 , s2
    = (r0 , s0) , (r2 , s2)

  D-pop-wf : {A : TU→Set}{n : ℕ}{t : T n}{a ty : U n}
           → (p : D A t ty)
           → WF (D-pop {a = a} p)
           → WF p
  D-pop-wf p ((x , y) , (hx , hy))
    with <M>-elim hx | <M>-elim hy
  ...| r0 , r1 , r2 | s0 , s1 , s2
    = (r0 , s0) , (r2 , s2)

  D-def-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}{F : U (suc n)}
           → (p : D A (ty ∷ t) F)
           → WF (D-def p)
           → WF p
  D-def-wf p ((x , y) , (hx , hy))
    with <M>-elim hx | <M>-elim hy
  ...| r0 , r1 , r2 | s0 , s1 , s2
    = (r0 , s0) , (r2 , s2)

  D-mu-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
          → (ps : List (Dμ A t ty))
          → WF (D-mu ps)
          → WFμ ps
  D-mu-wf ps ((xs , ys) , (hxs , hys))
    with Dμ-src ps
  ...| nothing = ⊥-elim (Maybe-⊥ (sym hxs))
  ...| just src
    with Dμ-dst ps
  ...| nothing = ⊥-elim (Maybe-⊥ (sym hys))
  ...| just dst
    = (src , dst) , refl , refl

  Dμ-[]-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
           → WFμ {A = A} {n} {t} {ty}  []
  Dμ-[]-wf = ([] , []) , (refl , refl)

  Dμ-ins-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
            → (a : ValU ty t)(ps : List (Dμ A t ty))
            → WFμ (Dμ-ins a ∷ ps)
            → WFμ ps
  Dμ-ins-wf a ps ((xs , ys) , (hxs , hys))
    with Dμ-dst ps
  ...| nothing = ⊥-elim (Maybe-⊥ (sym hys))
  ...| just dst = ((xs , dst) , (hxs , refl))

  Dμ-del-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
            → (a : ValU ty t)(ps : List (Dμ A t ty))
            → WFμ (Dμ-del a ∷ ps)
            → WFμ ps
  Dμ-del-wf a ps ((xs , ys) , (hxs , hys))
    with Dμ-src ps
  ...| nothing = ⊥-elim (Maybe-⊥ (sym hxs))
  ...| just src = ((src , ys) , (refl , hys))

  Dμ-dwn-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
            → (p : D A (u1 ∷ t) ty)(ps : List (Dμ A t ty))
            → WFμ (Dμ-dwn p ∷ ps)
            → WF p × WFμ ps
  Dμ-dwn-wf p ps ((xs , ys) , (hxs , hys))
    with D-src p | D-dst p
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hxs))
  ...| just sp | nothing = ⊥-elim (Maybe-⊥ (sym hys))
  ...| just sp | just dp
    with Dμ-src ps | Dμ-dst ps
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hxs))
  ...| just sps | nothing = ⊥-elim (Maybe-⊥ (sym hys))
  ...| just sps | just dps
    = ((sp , dp) , (refl , refl)) , (sps , dps) , (refl , refl)    
\end{code}

%<*Patch-WF-def>
\begin{code}
  Patch-WF : {n : ℕ} → TU→Set → T n → U n → Set
  Patch-WF A t ty = Σ (D A t ty) WF 
\end{code}
%</Patch-WF-def>
%<*Patch-mu-WF-def>
\begin{code}
  Patchμ-WF : {n : ℕ} → TU→Set → T n → U (suc n) → Set
  Patchμ-WF A t ty = Σ (List (Dμ A t ty)) WFμ
\end{code}
%</Patch-mu-WF-def>


%<*D-src-wf-type>
\begin{code}
  D-src-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
           → Patch-WF A t ty → ElU ty t
\end{code}
%</D-src-wf-type>
%<*D-src-wf-def>
\begin{code}
  D-src-wf (p , ((x , y) , (hx , hy))) = x
\end{code}
%</D-src-wf-def>

%<*D-dst-wf-type>
\begin{code}
  D-dst-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
           → Patch-WF A t ty → ElU ty t
\end{code}
%</D-dst-wf-type>
%<*D-dst-wf-def>
\begin{code}
  D-dst-wf (p , ((x , y) , (hx , hy))) = y
\end{code}
%</D-dst-wf-def>

%<*D-mu-src-wf-type>
\begin{code}
  Dμ-src-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
            → Patchμ-WF A t ty → List (ElU (μ ty) t)
\end{code}
%</D-mu-src-wf-type>
%<*D-mu-src-wf-def>
\begin{code}
  Dμ-src-wf (p , ((x , y) , (hx , hy))) = x
\end{code}
%</D-mu-src-wf-def>

%<*D-mu-dst-wf-type>
\begin{code}
  Dμ-dst-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
            → Patchμ-WF A t ty → List (ElU (μ ty) t)
\end{code}
%</D-mu-dst-wf-type>
%<*D-mu-dst-wf-def>
\begin{code}
  Dμ-dst-wf (p , ((x , y) , (hx , hy))) = y
\end{code}
%</D-mu-dst-wf-def>
