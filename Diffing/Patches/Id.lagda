\begin{code}
open import Prelude
open import Prelude.ListProperties
  using (lsplit-++-lemma; map-lemma; length-map
        ; lsplit-elim; lhead-elim)
open import Diffing.Universe
open import CF.Properties
  using (plug-correct; μ-ar-close-lemma; μ-open-ar-lemma; plug-spec-fgt
        ; plug-spec-ch)
open import Diffing.Patches.Cost
open import Diffing.Patches.D
open import Diffing.Patches.Properties.WellFormed
open import Diffing.Diff

module Diffing.Patches.Id where
\end{code}

  It is easy to check whether a diff is the identity
  diff of a given element or not. 
  This is a simple decidable property

\begin{code}
  mutual
\end{code}
%<*Is-diff-id-type>
\begin{code}
    Is-diff-id : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
               → (d : D A t ty) → Set
\end{code}
%</Is-diff-id-type>
\begin{code}
    Is-diff-id (D-A x) = ⊥
    Is-diff-id D-unit = Unit
    Is-diff-id (D-inl p) = Is-diff-id p
    Is-diff-id (D-inr p) = Is-diff-id p
    Is-diff-id (D-setl x x₁) = ⊥
    Is-diff-id (D-setr x x₁) = ⊥
    Is-diff-id (D-pair p q) = Is-diff-id p × Is-diff-id q
    Is-diff-id (D-mu x) = Is-diffL-id x × (x ≡ [] → ⊥)
    Is-diff-id (D-def p) = Is-diff-id p
    Is-diff-id (D-top p) = Is-diff-id p
    Is-diff-id (D-pop p) = Is-diff-id p
\end{code}
%<*Is-diffL-id-type>
\begin{code}
    Is-diffL-id : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
               → (d : List (Dμ A t ty)) → Set
\end{code}
%</Is-diffL-id-type>
\begin{code}
    Is-diffL-id [] = Unit
    Is-diffL-id (Dμ-A x ∷ p)   = ⊥
    Is-diffL-id (Dμ-ins x ∷ p) = ⊥
    Is-diffL-id (Dμ-del x ∷ p) = ⊥
    Is-diffL-id (Dμ-dwn dx ∷ p) = Is-diff-id dx × Is-diffL-id p
\end{code}

\begin{code}
  mutual
\end{code}
%<*Is-diff-id-dec-type>
\begin{code}
    Is-diff-id? : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
               → (d : D A t ty) → Dec (Is-diff-id d)
\end{code}
%</Is-diff-id-dec-type>
\begin{code}
    Is-diff-id? (D-A x) = no (λ ())
    Is-diff-id? D-unit = yes unit
    Is-diff-id? (D-inl p) = Is-diff-id? p
    Is-diff-id? (D-inr p) = Is-diff-id? p
    Is-diff-id? (D-setl x x₁) = no (λ z → z)
    Is-diff-id? (D-setr x x₁) = no (λ z → z)
    Is-diff-id? (D-pair p p₁)
      with Is-diff-id? p | Is-diff-id? p₁
    ...| no nop | _       = no (nop ∘ p1)
    ...| yes pp | no nop₁ = no (nop₁ ∘ p2)
    ...| yes pp | yes qq  = yes (pp , qq)
    Is-diff-id? (D-mu []) = no (λ z → p2 z refl)
    Is-diff-id? (D-mu (x ∷ xs))
      with Is-diffL-id? (x ∷ xs)
    ...| no  p = no (p ∘ p1)
    ...| yes p = yes (p , (λ ()))
    Is-diff-id? (D-def p) = Is-diff-id? p
    Is-diff-id? (D-top p) = Is-diff-id? p
    Is-diff-id? (D-pop p) = Is-diff-id? p
\end{code}
%<*Is-diffL-id-dec-type>
\begin{code}
    Is-diffL-id? : {A : TU→Set}{n : ℕ}{t : T n}{ty : U (suc n)}
                → (d : List (Dμ A t ty)) → Dec (Is-diffL-id d)
\end{code}
%</Is-diffL-id-dec-type>
\begin{code}
    Is-diffL-id? [] = yes unit
    Is-diffL-id? (Dμ-A x ∷ p)   = no (λ ())
    Is-diffL-id? (Dμ-ins x ∷ p) = no (λ z → z)
    Is-diffL-id? (Dμ-del x ∷ p) = no (λ z → z)
    Is-diffL-id? (Dμ-dwn x ∷ p)
      with Is-diff-id? x | Is-diffL-id? p
    ...| no  t | _ = no (t ∘ p1)
    ...| yes t | no  u = no (u ∘ p2)
    ...| yes t | yes u = yes (t , u)
\end{code}


  The identity patch is the same as (gdiff x x) but
  much easier to compute, as no comparisons are needed.

%<*gdiff-id-def>
\begin{code}
  mutual
    gdiff-id : {n : ℕ}{t : T n}{ty : U n}
             → (a : ElU ty t) → Patch t ty
    gdiff-id unit = D-unit
    gdiff-id (inl a) = D-inl (gdiff-id a)
    gdiff-id (inr a) = D-inr (gdiff-id a)
    gdiff-id (a1 , a2) = D-pair (gdiff-id a1) (gdiff-id a2)
    gdiff-id (top a) = D-top (gdiff-id a)
    gdiff-id (pop a) = D-pop (gdiff-id a)
    gdiff-id (red a) = D-def (gdiff-id a)
    gdiff-id (mu a) = D-mu (gdiffL-id (mu a ∷ []))
  
    {-# TERMINATING #-}
    gdiffL-id : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (as : List (ElU (μ ty) t)) → Patchμ t ty
    gdiffL-id [] = []
    gdiffL-id (x ∷ as)
     = Dμ-dwn (gdiff-id (μ-hd x)) ∷ gdiffL-id (μ-ch x ++ as)
\end{code}
%</gdiff-id-def>

  gdiff id has to have cost 0, as it is the identity.

\begin{code}
  mutual
\end{code}
%<*gdiff-id-cost-type>
\begin{code}
    gdiff-id-cost : {n : ℕ}{t : T n}{ty : U n}{c : Cost}
                  → (a : ElU ty t) → cost c (gdiff-id a) ≡ 0
\end{code}
%</gdiff-id-cost-type>
\begin{code}
    gdiff-id-cost unit = refl
    gdiff-id-cost (inl a) = gdiff-id-cost a
    gdiff-id-cost (inr a) = gdiff-id-cost a
    gdiff-id-cost {c = c} (a1 , a2) 
      = subst (λ P → P + cost c (gdiff-id a2) ≡ 0) 
              (sym (gdiff-id-cost a1)) (gdiff-id-cost a2)
    gdiff-id-cost (top a) = gdiff-id-cost a
    gdiff-id-cost (pop a) = gdiff-id-cost a
    gdiff-id-cost (mu a)
      = cong₂ _+_ (gdiff-id-cost (μ-hd (mu a)))
                  (gdiffL-id-cost (μ-ch (mu a) ++ [])) 
    gdiff-id-cost (red a) = gdiff-id-cost a 

    {-# TERMINATING #-}
    gdiffL-id-cost : {n : ℕ}{t : T n}{ty : U (suc n)}{c : Cost}
                  → (a : List (ElU (μ ty) t)) → costL c (gdiffL-id a) ≡ 0
    gdiffL-id-cost [] = refl
    gdiffL-id-cost {c = c} (a ∷ as) 
      = subst (λ P → P + costL c (gdiffL-id (μ-ch a ++ as)) ≡ 0) 
              (sym (gdiff-id-cost (μ-hd a))) 
              (gdiffL-id-cost (μ-ch a ++ as))
\end{code}

  It turns out that we were indeed correct in computing our diff-id:

\begin{code}
  private
    helper1 : {n : ℕ}{t : T n}{ty : U (suc n)}
            → (x : ElU ty (μ ty ∷ t))
            → ar 0 (fgt 0 x) ≡ length (map unpop (ch 0 x))
    helper1 x = sym (μ-open-ar-lemma (mu x))
\end{code}

\begin{code}
  mutual
    {-# TERMINATING #-}
\end{code}
%<*gdiff-id-correct-type>
\begin{code}
    gdiff-id-src-lemma 
      : {n : ℕ}{t : T n}{ty : U n}
      → (x : ElU ty t) → D-src (gdiff-id x) ≡ just x
\end{code}
%</gdiff-id-correct-type>
%<*gdiffL-id-correct-type>
\begin{code}
    gdiffL-id-src-lemma 
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (xs : List (ElU (μ ty) t)) → Dμ-src (gdiffL-id xs) ≡ just xs
\end{code}
%</gdiffL-id-correct-type>
\begin{code}
    gdiff-id-src-lemma unit = refl
    gdiff-id-src-lemma (inl x) = <M>-intro (gdiff-id-src-lemma x)
    gdiff-id-src-lemma (inr x) = <M>-intro (gdiff-id-src-lemma x)
    gdiff-id-src-lemma (x , x₁)
      rewrite gdiff-id-src-lemma x
            | gdiff-id-src-lemma x₁
            = refl
    gdiff-id-src-lemma (top x) = <M>-intro (gdiff-id-src-lemma x)
    gdiff-id-src-lemma (pop x) = <M>-intro (gdiff-id-src-lemma x)
    gdiff-id-src-lemma (red x) = <M>-intro (gdiff-id-src-lemma x)
    gdiff-id-src-lemma {ty = μ ty} (mu x)
      rewrite gdiffL-id-src-lemma (μ-ch (mu x) ++ [])
            | gdiff-id-src-lemma (fgt 0 x)
            | μ-ar-close-lemma (mu x) []
            | helper1 x
            | lsplit-++-lemma (map unpop (ch 0 x)) []
            | map-lemma {f = unpop} {g = pop {a = μ ty}} (ch 0 x) (λ { (pop x) → refl })
            | sym (plug-correct 0 x)
            = refl

    gdiffL-id-src-lemma [] = refl
    gdiffL-id-src-lemma {ty = ty} (mu x ∷ xs)
      rewrite gdiff-id-src-lemma (μ-hd (mu x))
            | gdiffL-id-src-lemma (μ-ch (mu x) ++ xs)
            | μ-ar-close-lemma (mu x) xs
            | helper1 x
            | lsplit-++-lemma (map unpop (ch 0 x)) xs
            | map-lemma {f = unpop} {g = pop {a = μ ty}} (ch 0 x) (λ { (pop x) → refl })
            | sym (plug-correct 0 x)
            = refl
\end{code}

\begin{code}
  mutual
    {-# TERMINATING #-}
\end{code}
%<*gdiff-id-correct-type>
\begin{code}
    gdiff-id-dst-lemma 
      : {n : ℕ}{t : T n}{ty : U n}
      → (x : ElU ty t) → D-dst (gdiff-id x) ≡ just x
\end{code}
%</gdiff-id-correct-type>
%<*gdiffL-id-correct-type>
\begin{code}
    gdiffL-id-dst-lemma 
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (xs : List (ElU (μ ty) t)) → Dμ-dst (gdiffL-id xs) ≡ just xs
\end{code}
%</gdiffL-id-correct-type>
\begin{code}
    gdiff-id-dst-lemma unit = refl
    gdiff-id-dst-lemma (inl x) = <M>-intro (gdiff-id-dst-lemma x)
    gdiff-id-dst-lemma (inr x) = <M>-intro (gdiff-id-dst-lemma x)
    gdiff-id-dst-lemma (x , x₁)
      rewrite gdiff-id-dst-lemma x
            | gdiff-id-dst-lemma x₁
            = refl
    gdiff-id-dst-lemma (top x) = <M>-intro (gdiff-id-dst-lemma x)
    gdiff-id-dst-lemma (pop x) = <M>-intro (gdiff-id-dst-lemma x)
    gdiff-id-dst-lemma (red x) = <M>-intro (gdiff-id-dst-lemma x)
    gdiff-id-dst-lemma {ty = μ ty} (mu x)
      rewrite gdiffL-id-dst-lemma (μ-ch (mu x) ++ [])
            | gdiff-id-dst-lemma (fgt 0 x)
            | μ-ar-close-lemma (mu x) []
            | helper1 x
            | lsplit-++-lemma (map unpop (ch 0 x)) []
            | map-lemma {f = unpop} {g = pop {a = μ ty}} (ch 0 x) (λ { (pop x) → refl })
            | sym (plug-correct 0 x)
            = refl

    gdiffL-id-dst-lemma [] = refl
    gdiffL-id-dst-lemma {ty = ty} (mu x ∷ xs)
      rewrite gdiff-id-dst-lemma (μ-hd (mu x))
            | gdiffL-id-dst-lemma (μ-ch (mu x) ++ xs)
            | μ-ar-close-lemma (mu x) xs
            | helper1 x
            | lsplit-++-lemma (map unpop (ch 0 x)) xs
            | map-lemma {f = unpop} {g = pop {a = μ ty}} (ch 0 x) (λ { (pop x) → refl })
            | sym (plug-correct 0 x)
            = refl
\end{code}

  Hence, gdiff-id is well-founded

\begin{code}
  gdiff-id-wf : {n : ℕ}{t : T n}{ty : U n}
              → (x : ElU ty t)
              → WF (gdiff-id x)
  gdiff-id-wf x = ((x , x) , gdiff-id-src-lemma x , gdiff-id-dst-lemma x)
\end{code}

  Now we just need to relate Is-diff-id? with gdiff-id.

\begin{code}
  is-diff-id-correct
    : {n : ℕ}{t : T n}{ty : U n}
    → (p : Patch t ty)(wfp : WF p)(hip : Is-diff-id p)
    → ∃ (λ x → p ≡ gdiff-id x)

  is-diffL-id-correct
    : {n : ℕ}{t : T n}{ty : U (suc n)}
    → (p : Patchμ t ty)(wfp : WFμ p)(hip : Is-diffL-id p)
    → ∃ (λ x → p ≡ gdiffL-id x)

  is-diff-id-correct (D-A ()) wf hip
  is-diff-id-correct D-unit wf hip = unit , refl
  is-diff-id-correct (D-inl p) wf hip 
    = (inl ×' cong D-inl) (is-diff-id-correct p (D-inl-wf p wf) hip)
  is-diff-id-correct (D-inr p) wf hip 
    = (inr ×' cong D-inr) (is-diff-id-correct p (D-inr-wf p wf) hip)
  is-diff-id-correct (D-setl x x₁) wf ()
  is-diff-id-correct (D-setr x x₁) wf ()
  is-diff-id-correct (D-pair p q) wf (hp , hq) 
    = let xq , pq = is-diff-id-correct q (p2 (D-pair-wf p q wf)) hq
          xp , pp = is-diff-id-correct p (p1 (D-pair-wf p q wf)) hp
       in (xp , xq) , cong₂ D-pair pp pq
  is-diff-id-correct (D-def p) wf hip
    = (red ×' cong D-def) (is-diff-id-correct p (D-def-wf p wf) hip)
  is-diff-id-correct (D-top p) wf hip
    = (top ×' cong D-top) (is-diff-id-correct p (D-top-wf p wf) hip)
  is-diff-id-correct (D-pop p) wf hip
    = (pop ×' cong D-pop) (is-diff-id-correct p (D-pop-wf p wf) hip)
  is-diff-id-correct (D-mu x) wf hip 
    with is-diffL-id-correct x (D-mu-wf x wf) (p1 hip)
  ...| xs , prf
    with wf
  ...| (mu s , d) , (ps , pd)
    rewrite prf | gdiffL-id-src-lemma xs | lhead-elim xs ps
      = mu s , refl

  is-diffL-id-correct [] wf hip = [] , refl
  is-diffL-id-correct (Dμ-A () ∷ p) wf hip
  is-diffL-id-correct (Dμ-ins x ∷ p) wf ()
  is-diffL-id-correct (Dμ-del x ∷ p) wf ()
  is-diffL-id-correct (Dμ-dwn x ∷ p) wf (hx , hp) 
    with is-diff-id-correct x (p1 (Dμ-dwn-wf x p wf)) hx
       | is-diffL-id-correct p (p2 (Dμ-dwn-wf x p wf)) hp
  ...| xx , px | xp , pp rewrite px | pp
    with wf
  ...| (swf , dwf) , (hs , hd) 
    rewrite gdiff-id-src-lemma xx 
          | gdiffL-id-src-lemma xp
    with ar 0 xx ≤?-ℕ length xp
  ...| no  _ = ⊥-elim (Maybe-⊥ (sym hs))
  ...| yes _ 
    with lsplit (ar 0 xx) xp | inspect (lsplit (ar 0 xx)) xp
  ...| xp0 , xp1 | [ XP ] 
    with plug 0 xx (map pop xp0) | inspect (plug 0 xx) (map pop xp0)
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hs))
  ...| just x' | [ X' ] 
    = swf 
    , sym (trans 
      (cong gdiffL-id (just-inj (sym hs))) 
      (cong₂ (λ P Q → Dμ-dwn (gdiff-id P) ∷ gdiffL-id Q) 
             (plug-spec-fgt 0 x' xx (map pop xp0) X') 
             (sym (trans (lsplit-elim (ar 0 xx) xp XP) 
                         ((cong (λ P → P ++ xp1) 
                          (sym (trans (cong (map unpop) (plug-spec-ch 0 x' xx (map pop xp0) X'))
                                  (map-lemma xp0 (λ _ → refl))))))))))
\end{code}

\begin{code}
  idid-cost-lemma
    : {n : ℕ}{t : T n}{ty : U n}{Δ : Cost}
    → (p : Patch t ty)(wf : WF p)(hip : Is-diff-id p)
    → cost Δ p ≡ 0
  idid-cost-lemma p wf hip 
    with is-diff-id-correct p wf hip
  ...| x , px rewrite px = gdiff-id-cost x

  ididμ-cost-lemma
    : {n : ℕ}{t : T n}{ty : U (suc n)}{Δ : Cost}
    → (p : Patchμ t ty)(wf : WFμ p)(hip : Is-diffL-id p)
    → costL Δ p ≡ 0
  ididμ-cost-lemma p wf hip 
    with is-diffL-id-correct p wf hip
  ...| x , px rewrite px = gdiffL-id-cost x
\end{code}

\begin{code}
  idid-dst-src-lemma 
    : {n : ℕ}{t : T n}{ty : U n}{Δ : Cost}
    → (p : Patch t ty)(wf : WF p)(hip : Is-diff-id p)
    → D-dst p ≡ D-src p
  idid-dst-src-lemma p wf hip
    with is-diff-id-correct p wf hip
  ...| x , px rewrite px 
    = trans (gdiff-id-dst-lemma x) (sym (gdiff-id-src-lemma x))

  ididμ-dst-src-lemma 
    : {n : ℕ}{t : T n}{ty : U (suc n)}{Δ : Cost}
    → (p : Patchμ t ty)(wf : WFμ p)(hip : Is-diffL-id p)
    → Dμ-dst p ≡ Dμ-src p
  ididμ-dst-src-lemma p wf hip
    with is-diffL-id-correct p wf hip
  ...| x , px rewrite px 
    = trans (gdiffL-id-dst-lemma x) (sym (gdiffL-id-src-lemma x))
\end{code}
