\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches1.Diff
open import Diffing.Patches1.Diff.Functor
open import Diffing.Patches1.Conflicts
open import Diffing.Patches1.Residual

module Diffing.Patches1.Residual.Symmetry where
\end{code}

  An interesting observation, though, is that if (p / q) ≡ just k,
  then (q / p) ≡ just i, with i ≡ fmap C-sym (op k), for some op.

  What does this mean? 

  Well, we just need to solve the conflicts of (p / q),
  and this solution can translated to a solution of the
  conflicts present in (q / p).
  
  The result is existentially quantified over an operation
  as, for instance, if we delete something in (p / q) but not in (q / p),
  we need to ignore this deleting operation when translating the residuals,
  therefore they are not really equal. The important part
  is that their conflicts, modulo op, are symmetric.  

\begin{code}
  open import Relation.Binary.PropositionalEquality

  on-tail : ∀{a}{A : Set a} → (List A → List A) → List A → List A
  on-tail f [] = []
  on-tail f (x ∷ xs) = x ∷ f xs

  on-tail-kill : ∀{a}{A : Set a} → (List A → List A) → List A → List A
  on-tail-kill f [] = []
  on-tail-kill f (x ∷ xs) = f xs

  hd-tail : ∀{a}{A : Set a} → (A → A) → (List A → List A) → List A → List A
  hd-tail f tl [] = []
  hd-tail f tl (x ∷ xs) = f x ∷ tl xs

  private
    mutual
      aux : {n : ℕ}{t : Tel n}{ty : U n}{k : D C t ty}
          → (d1 d2 : Patch t ty) 
          → d1 / d2 ≡ just k
          → Σ (D C t ty → D C t ty) 
              (λ op → d2 / d1 ≡ just (D-map C-sym (op k)))
      aux (D-A ()) _ _
      aux _ (D-A ()) _

      aux D-id d prf rewrite sym (just-inj prf) 
        = const (cast d) 
        , trans (/-id d) (cong just (sym (D-map-cast C-sym d)))

      aux p D-id prf rewrite sym prf
        = const D-id , refl 

      aux D-void D-void refl = id , refl

      aux (D-inl d1) (D-inl d2) prf with <M>-elim prf
      ...| r , refl , q with aux d1 d2 q
      ...| op , hip = (λ { (D-inl x) → D-inl (op x) ; x → x } ) 
                    , <M>-intro hip
      aux (D-inl d1) (D-setl xa xb) prf with gapply d1 xa
      aux (D-inl d1) (D-setl xa xb) () | nothing
      ...| just xa' with xa ≟-U xa'
      ...| yes _ rewrite sym (just-inj prf) = id , refl
      ...| no  _ rewrite sym (just-inj prf) = id , refl
      aux (D-setl xa xb) (D-inl d2) prf with gapply d2 xa
      aux (D-setl xa xb) (D-inl d2) () | nothing
      ...| just xa' with xa ≟-U xa'
      ...| yes _ rewrite sym (just-inj prf) = id , refl
      ...| no  _ rewrite sym (just-inj prf) = id , refl
      aux (D-setl xa xb) (D-setl ya yb) prf with xa ≟-U ya | ya ≟-U xa
      aux (D-setl xa xb) (D-setl ya yb) () | no ¬p | no  _
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | yes _ with xb ≟-U yb | yb ≟-U xb
      ...| yes q | no ¬q = ⊥-elim (¬q (sym q))
      ...| no ¬q | yes q = ⊥-elim (¬q (sym q))
      ...| yes q | yes _ 
         = id , cong just 
                (subst (λ P → D-setl ya yb ≡ D-map C-sym P) 
                  (just-inj prf) (cong₂ D-setl (sym p) (sym q)))
      ...| no ¬q | no  _  rewrite p | sym (just-inj prf) = id , refl

      aux (D-inr d1) (D-inr d2) prf with <M>-elim prf
      ...| r , refl , q with aux d1 d2 q
      ...| op , hip = (λ { (D-inr x) → D-inr (op x) ; x → x } ) 
                    , <M>-intro hip
      aux (D-inr d1) (D-setr xa xb) prf with gapply d1 xa
      aux (D-inr d1) (D-setr xa xb) () | nothing
      ...| just xa' with xa ≟-U xa'
      ...| yes _ rewrite sym (just-inj prf) = id , refl
      ...| no  _ rewrite sym (just-inj prf) = id , refl
      aux (D-setr xa xb) (D-inr d2) prf with gapply d2 xa
      aux (D-setr xa xb) (D-inr d2) () | nothing
      ...| just xa' with xa ≟-U xa'
      ...| yes _ rewrite sym (just-inj prf) = id , refl
      ...| no  _ rewrite sym (just-inj prf) = id , refl
      aux (D-setr xa xb) (D-setr ya yb) prf with xa ≟-U ya | ya ≟-U xa
      aux (D-setr xa xb) (D-setr ya yb) () | no ¬p | no  _
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | yes _ with xb ≟-U yb | yb ≟-U xb
      ...| yes q | no ¬q = ⊥-elim (¬q (sym q))
      ...| no ¬q | yes q = ⊥-elim (¬q (sym q))
      ...| yes q | yes _ 
         = id , cong just 
                 (subst (λ P → D-setr ya yb ≡ D-map C-sym P) 
                   (just-inj prf) (cong₂ D-setr (sym p) (sym q)))
      ...| no ¬q | no  _  rewrite p | sym (just-inj prf) = id , refl

      aux (D-inl d1) (D-inr d2) ()
      aux (D-inl d1) (D-setr xa xb) ()
      aux (D-inr d1) (D-inl d2) ()
      aux (D-inr d1) (D-setl x x₁) ()  
      aux (D-setl xa xb) (D-inr d2) ()      
      aux (D-setl xa xb) (D-setr ya yb) ()
      aux (D-setr xa xb) (D-inl d2) ()     
      aux (D-setr xa xb) (D-setl ya yb) ()

      aux (D-pair d1 d2) (D-pair d3 d4) prf 
        with <M*>-elim-full {f = D-pair <M> (d1 / d3)} {x = d2 / d4} prf
      ...| (f1 , a1) , p1 , refl , q1 with <M>-elim p1
      ...| r1 , r2 , r3 with aux d1 d3 r3 | aux d2 d4 q1
      ...| op1 , hip1 | op2 , hip2 rewrite hip1 | hip2 | r2 
         = (λ { (D-pair m n) → D-pair (op1 m) (op2 n) ; x → x }) 
         , refl

      aux (D-β d1) (D-β d2) prf with <M>-elim prf
      ...| r , refl , q with aux d1 d2 q
      ...| op , res = (λ { (D-β x) → D-β (op x) ; x → x })
                    , <M>-intro res   
      aux (D-top d1) (D-top d2) prf with <M>-elim prf
      ...| r , refl , q with aux d1 d2 q
      ...| op , res = (λ { (D-top x) → D-top (op x) ; x → x })
                    , <M>-intro res   
      aux (D-pop d1) (D-pop d2) prf with <M>-elim prf
      ...| r , refl , q with aux d1 d2 q
      ...| op , res = (λ { (D-pop x) → D-pop (op x) ; x → x })
                    , <M>-intro res   
      aux (D-mu d1) (D-mu d2) prf with <M>-elim prf
      ...| r , refl , q with aux* d1 d2 q
      ...| op , res = (λ { (D-mu x) → D-mu (op x) ; x → x })
                    , <M>-intro res            

      aux* : {n : ℕ}{t : Tel n}{ty : U (suc n)}{k : List (Dμ C t ty)}
           → (d1 d2 : Patchμ t ty) 
           → res d1 d2 ≡ just k
           → Σ (List (Dμ C t ty) → List (Dμ C t ty)) 
               (λ op → res d2 d1 ≡ just (Dμ-map C-sym (op k)))
      aux* (Dμ-A () ∷ _) _ prf
      aux* _ (Dμ-A () ∷ _) prf

      aux* [] [] refl = id , refl

      aux* (Dμ-ins x ∷ d1) (Dμ-ins y ∷ d2) prf with x ≟-U y | y ≟-U x
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      aux* (Dμ-ins x ∷ d1) (Dμ-ins y ∷ d2) prf | no ¬p | no _ 
        with <M>-elim prf
      ...| r , refl , q with aux* d1 d2 q
      ...| op , hip = on-tail op , <M>-intro hip
      aux* (Dμ-ins x ∷ d1) (Dμ-ins .x ∷ d2) prf | yes refl | yes _ 
        with <M>-elim prf
      ...| r , refl , q with aux* d1 d2 q
      ...| op , hip = on-tail op , <M>-intro hip

      aux* (Dμ-ins x ∷ d1) [] prf with <M>-elim prf
      ...| r , refl , p with aux* d1 [] p 
      ...| op , hip = on-tail op , <M>-intro hip
      aux* [] (Dμ-ins x ∷ d2) prf with <M>-elim prf
      ...| r , refl , p with aux* [] d2 p
      ...| op , hip = on-tail op , <M>-intro hip

      aux* (Dμ-ins x ∷ d1) (Dμ-del y ∷ d2) prf with <M>-elim prf
      ...| r , refl , p with aux* d1 (Dμ-del y ∷ d2) p 
      ...| op , hip = on-tail op , <M>-intro hip
      aux* (Dμ-ins x ∷ d1) (Dμ-cpy y ∷ d2) prf with <M>-elim prf
      ...| r , refl , p with aux* d1 (Dμ-cpy y ∷ d2) p 
      ...| op , hip = on-tail op , <M>-intro hip
      aux* (Dμ-ins x ∷ d1) (Dμ-dwn y dy ∷ d2) prf with <M>-elim prf
      ...| r , refl , p with aux* d1 (Dμ-dwn y dy ∷ d2) p 
      ...| op , hip = on-tail op , <M>-intro hip

      aux* (Dμ-del x ∷ d1) (Dμ-ins y ∷ d2) prf with <M>-elim prf
      ...| r , refl , p with aux* (Dμ-del x ∷ d1) d2 p 
      ...| op , hip = on-tail op , <M>-intro hip
      aux* (Dμ-cpy x ∷ d1) (Dμ-ins y ∷ d2) prf with <M>-elim prf
      ...| r , refl , p with aux* (Dμ-cpy x ∷ d1) d2 p 
      ...| op , hip = on-tail op , <M>-intro hip
      aux* (Dμ-dwn x dx ∷ d1) (Dμ-ins y ∷ d2) prf with <M>-elim prf
      ...| r , refl , p with aux* (Dμ-dwn x dx ∷ d1) d2 p 
      ...| op , hip = on-tail op , <M>-intro hip

      aux* [] (Dμ-del x ∷ d2) ()
      aux* [] (Dμ-cpy x ∷ d2) ()
      aux* [] (Dμ-dwn x dx ∷ d2) ()
      aux* (Dμ-del x ∷ d1) [] ()
      aux* (Dμ-cpy x ∷ d1) [] ()
      aux* (Dμ-dwn x dx ∷ d1) [] ()

      aux* (Dμ-del x ∷ d1) (Dμ-del y ∷ d2) prf with x ≟-U y | y ≟-U x
      aux* (Dμ-del x ∷ d1) (Dμ-del y ∷ d2) () | no ¬p | no _
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      ...| yes p | yes _ = aux* d1 d2 prf

      aux* (Dμ-del x ∷ d1) (Dμ-cpy y ∷ d2) prf with x ≟-U y | y ≟-U x
      aux* (Dμ-del x ∷ d1) (Dμ-cpy y ∷ d2) () | no ¬p | no _
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      ...| yes p | yes _ with <M>-elim prf
      ...| r , refl , q with aux* d1 d2 q
      ...| op , hip = on-tail-kill op , hip
      aux* (Dμ-cpy x ∷ d1) (Dμ-del y ∷ d2) prf with x ≟-U y | y ≟-U x
      aux* (Dμ-cpy x ∷ d1) (Dμ-del y ∷ d2) () | no ¬p | no _
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      ...| yes p | yes _  with aux* d1 d2 prf
      ...| op , hip = (_∷_ (Dμ-del y) ∘ op) , (<M>-intro hip)

      aux* (Dμ-del x ∷ d1) (Dμ-dwn y dy ∷ d2) prf with x ≟-U y | y ≟-U x
      aux* (Dμ-del x ∷ d1) (Dμ-dwn y dy ∷ d2) () | no ¬p | no _
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      aux* (Dμ-del .y ∷ d1) (Dμ-dwn y dy ∷ d2) prf | yes refl | yes _ 
        with gapply dy (red y)
      aux* (Dμ-del .y ∷ d1) (Dμ-dwn y dy ∷ d2) () | yes refl | yes p | nothing
      ...| just (red y') with <M>-elim prf
      ...| r , refl , q with aux* d1 d2 q
      ...| op , hip = on-tail op , <M>-intro hip

      aux* (Dμ-cpy x ∷ d1) (Dμ-cpy y ∷ d2) prf with x ≟-U y | y ≟-U x
      aux* (Dμ-cpy x ∷ d1) (Dμ-cpy y ∷ d2) () | no ¬p | no _
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      aux* (Dμ-cpy x ∷ d1) (Dμ-cpy .x ∷ d2) prf | yes refl | yes _ with <M>-elim prf
      ...| r , refl , q with aux* d1 d2 q
      ...| op , hip = (on-tail op) , <M>-intro hip

      aux* (Dμ-cpy x ∷ d1) (Dμ-dwn y dy ∷ d2) prf with x ≟-U y | y ≟-U x
      aux* (Dμ-cpy x ∷ d1) (Dμ-dwn y dy ∷ d2) () | no ¬p | no _
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      aux* (Dμ-cpy .y ∷ d1) (Dμ-dwn y dy ∷ d2) prf | yes refl | yes _ 
        with gapply dy (red y)
      aux* (Dμ-cpy .y ∷ d1) (Dμ-dwn y dy ∷ d2) () | yes refl | yes _ | nothing 
      ...| just (red y') with <M>-elim prf
      ...| r , refl , q with aux* d1 d2 q
      ...| op , hip = (hd-tail (const (Dμ-dwn y (D-map C-sym (cast dy)))) op) 
           , trans (<M>-intro hip) 
               (cong just (cong (λ P → P ∷ Dμ-map C-sym (op r)) 
                 (cong (Dμ-dwn y) (sym (trans (D-map-join C-sym C-sym (cast dy)) 
                   (D-map-cast (λ {m} {t'} {ty'} z → C-sym (C-sym z)) dy))))))

      aux* (Dμ-dwn x dx ∷ d1) (Dμ-del y ∷ d2) prf with x ≟-U y | y ≟-U x
      aux* (Dμ-dwn x dx ∷ d1) (Dμ-del y ∷ d2) () | no ¬p | no _
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      aux* (Dμ-dwn x dx ∷ d1) (Dμ-del .x ∷ d2) prf | yes refl | yes _ 
        with gapply dx (red x)
      aux* (Dμ-dwn x dx ∷ d1) (Dμ-del .x ∷ d2) () | yes refl | yes _ | nothing
      ...| just (red x') with <M>-elim prf
      ...| r , refl , q with aux* d1 d2 q
      ...| op , hip = (on-tail op) , (<M>-intro hip)

      aux* (Dμ-dwn x dx ∷ d1) (Dμ-cpy y ∷ d2) prf with x ≟-U y | y ≟-U x
      aux* (Dμ-dwn x dx ∷ d1) (Dμ-cpy y ∷ d2) () | no ¬p | no _
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      aux* (Dμ-dwn x dx ∷ d1) (Dμ-cpy .x ∷ d2) prf | yes refl | yes _ 
        with gapply dx (red x)
      aux* (Dμ-dwn x dx ∷ d1) (Dμ-cpy .x ∷ d2) () | yes refl | yes _ | nothing
      ...| just (red x') with <M>-elim prf
      ...| r , refl , q with aux* d1 d2 q
      ...| op , hip = (hd-tail (const (Dμ-cpy x')) op) , (<M>-intro hip)

      aux* (Dμ-dwn x dx ∷ d1) (Dμ-dwn y dy ∷ d2) prf with x ≟-U y | y ≟-U x
      aux* (Dμ-dwn x dx ∷ d1) (Dμ-dwn y dy ∷ d2) () | no ¬p | no _
      ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
      ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
      aux* (Dμ-dwn x dx ∷ d1) (Dμ-dwn .x dy ∷ d2) prf | yes refl | yes _ 
        with <M*>-elim {x = res d1 d2} prf
      ...| (f1 , x1) , (p1 , p2) rewrite p1 
         with <M>-elim (<M*>-to-<M> {f = f1} {x = res d1 d2} prf)
      ...| r , refl , q with aux* d1 d2 q
      ...| op , hip with <M>-elim p1
      ...| rp1 , pp1 , qp1 with <M>-elim qp1
      ...| rqp1 , pqp1 , qqp1 with aux dx dy qqp1
      ...| opHd , hipHd rewrite hipHd | pp1 
         = hd-tail (const (Dμ-dwn x (opHd rqp1))) op 
         , <M>-to-<M*> (<M>-intro hip)
\end{code}

%<*residual-symmetry-type>
\begin{code}
  residual-symmetry-thm
    : {n : ℕ}{t : Tel n}{ty : U n}{k : D C t ty}
    → (d1 d2 : Patch t ty) 
    → d1 / d2 ≡ just k
    → Σ (D C t ty → D C t ty) 
        (λ op → d2 / d1 ≡ just (D-map C-sym (op k)))
\end{code}
%</residual-symmetry-type>
\begin{code}
  residual-symmetry-thm = aux
\end{code}

%<*residualμ-symmetry-type>
\begin{code}
  residualμ-symmetry-thm
    : {n : ℕ}{t : Tel n}{ty : U (suc n)}{k : List (Dμ C t ty)}
    → (d1 d2 : Patchμ t ty) 
    → res d1 d2 ≡ just k
    → Σ (List (Dμ C t ty) → List (Dμ C t ty)) 
        (λ op → res d2 d1 ≡ just (Dμ-map C-sym (op k)))
\end{code}
%</residualμ-symmetry-type>
\begin{code}
  residualμ-symmetry-thm = aux*
\end{code}

%<*residual-nothing-type>
\begin{code}
  residual-nothing 
    : {n : ℕ}{t : Tel n}{ty : U n}
    → (d1 d2 : Patch t ty) 
    → d1 / d2 ≡ nothing
    → d2 / d1 ≡ nothing
\end{code}
%</residual-nothing-type>
\begin{code}
  residual-nothing d1 d2 prf with d2 / d1 | inspect (_/_ d2) d1
  ...| nothing | [ R ] = refl
  ...| just d21 | [ R ] with residual-symmetry-thm d2 d1 R
  ...| op , d12 = ⊥-elim (Maybe-⊥ (trans (sym d12) prf))
\end{code}
