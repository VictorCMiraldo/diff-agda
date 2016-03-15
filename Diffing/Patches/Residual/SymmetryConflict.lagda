\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff
open import Diffing.Patches.Diff.Functor
open import Diffing.Patches.Diff.Id
open import Diffing.Patches.Conflicts
open import Diffing.Patches.Residual
open import Diffing.Patches.Residual.Symmetry

module Diffing.Patches.Residual.SymmetryConflict where
\end{code}

  The residual symmetry theorem does not guarantee that the symmetric
  residual will not introduce anymore conflicts. We don't know anything
  about that operation, which the theorem speaks of.

  This theorem specifies exactly that! Now we have a perfectly
  sound way of solving the conflicts of (d2 / d1), after solving
  the conflicts of (d1 / d2).

\begin{code}
  {-# TERMINATING #-}
\end{code}
%<*residual-sym-stable-type>
\begin{code}
  residual-sym-stable : {n : ℕ}{t : Tel n}{ty : U n}{k : D C t ty}
    → (d1 d2 : Patch t ty) 
    → d1 / d2 ≡ just k
    → forget <$> (d2 / d1) ≡ just (map (↓-map-↓ C-sym) (forget k)) 
\end{code}
%</residual-sym-stable-type>
\begin{code}
  residual-sym-stable = aux
    where
      open import Data.List.Properties using (map-++-commute)

      mutual
        {-# TERMINATING #-}
        aux : {n : ℕ}{t : Tel n}{ty : U n}{k : D C t ty}
            → (d1 d2 : Patch t ty) 
            → d1 / d2 ≡ just k
            → forget <M> (d2 / d1) ≡ just (map (↓-map-↓ C-sym) (forget k)) 
        aux (D-A ()) _ _
        aux _ (D-A ()) _

        aux D-unit D-unit refl = refl

        aux (D-inl d1) (D-inl d2) prf with <M>-elim prf
        ...| r1 , refl , q1 with <M>-elim (aux d1 d2 q1)
        ...| r2 , s2 , q2 rewrite q2 = cong just (sym s2)
        aux (D-inl d1) (D-setl xa xb) prf with gapply d1 xa
        aux (D-inl d1) (D-setl xa xb) () | nothing
        ...| just xa' with xa ≟-U xa'
        ...| yes p rewrite sym (just-inj prf) = refl
        ...| no ¬p rewrite sym (just-inj prf) = refl  
        aux (D-setl xa xb) (D-inl d2) prf with gapply d2 xa
        aux (D-setl xa xb) (D-inl d2) () | nothing
        ...| just xa' with xa ≟-U xa'
        ...| yes p rewrite sym (just-inj prf) = refl
        ...| no ¬p rewrite sym (just-inj prf) = refl
        aux (D-setl xa xb) (D-setl ya yb) prf with xa ≟-U ya | ya ≟-U xa
        ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
        ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
        aux (D-setl xa xb) (D-setl ya yb) () | no ¬p | no ¬p₁
        ...| yes p | yes _ with xb ≟-U yb | yb ≟-U xb
        ...| no ¬q | yes q = ⊥-elim (¬q (sym q))
        ...| yes q | no ¬q = ⊥-elim (¬q (sym q))
        ...| no ¬q | no _ rewrite p | sym (just-inj prf) = refl
        ...| yes q | yes _ rewrite sym (just-inj prf) = refl

        aux (D-inr d1) (D-inr d2) prf with <M>-elim prf
        ...| r1 , refl , q1 with <M>-elim (aux d1 d2 q1)
        ...| r2 , s2 , q2 rewrite q2 = cong just (sym s2)
        aux (D-inr d1) (D-setr xa xb) prf with gapply d1 xa
        aux (D-inr d1) (D-setr xa xb) () | nothing
        ...| just xa' with xa ≟-U xa'
        ...| yes p rewrite sym (just-inj prf) = refl
        ...| no ¬p rewrite sym (just-inj prf) = refl  
        aux (D-setr xa xb) (D-inr d2) prf with gapply d2 xa
        aux (D-setr xa xb) (D-inr d2) () | nothing
        ...| just xa' with xa ≟-U xa'
        ...| yes p rewrite sym (just-inj prf) = refl
        ...| no ¬p rewrite sym (just-inj prf) = refl
        aux (D-setr xa xb) (D-setr ya yb) prf with xa ≟-U ya | ya ≟-U xa
        ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
        ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
        aux (D-setr xa xb) (D-setr ya yb) () | no ¬p | no ¬p₁
        ...| yes p | yes _ with xb ≟-U yb | yb ≟-U xb
        ...| no ¬q | yes q = ⊥-elim (¬q (sym q))
        ...| yes q | no ¬q = ⊥-elim (¬q (sym q))
        ...| no ¬q | no _ rewrite p | sym (just-inj prf) = refl
        ...| yes q | yes _ rewrite sym (just-inj prf) = refl
        
        aux (D-inl d1) (D-inr d2) ()
        aux (D-inl d1) (D-setr xa xb) ()
        aux (D-inr d1) (D-inl d2) ()
        aux (D-inr d1) (D-setl x x₁) ()  
        aux (D-setl xa xb) (D-inr d2) ()      
        aux (D-setl xa xb) (D-setr ya yb) ()
        aux (D-setr xa xb) (D-inl d2) ()     
        aux (D-setr xa xb) (D-setl ya yb) ()
        
        aux (D-pair d1 d2) (D-pair d3 d4) prf
          with <M*>-elim-full {x = d2 / d4} prf 
        ...| (fa , a) , r1 , s1 , q1 with <M>-elim r1
        ...| s2 , r2 , q2 with <M>-elim (aux d1 d3 q2)
        ...| s3 , r3 , q3 rewrite q3 with <M>-elim (aux d2 d4 q1)
        ...| s4 , r4 , q4 rewrite q4 | r2 | s1 
           = cong just (trans (cong₂ _++_ (sym r3) (sym r4))
                          (sym (map-++-commute (↓-map-↓ C-sym) (forget s2) (forget a))))

        aux (D-def d1) (D-def d2) prf with <M>-elim prf
        ...| r1 , refl , q1 with <M>-elim (aux d1 d2 q1)
        ...| r2 , s2 , q2 rewrite q2 = cong just (sym s2)   
        aux (D-top d1) (D-top d2) prf with <M>-elim prf
        ...| r1 , refl , q1 with <M>-elim (aux d1 d2 q1)
        ...| r2 , s2 , q2 rewrite q2 = cong just (sym s2)   
        aux (D-pop d1) (D-pop d2) prf with <M>-elim prf
        ...| r1 , refl , q1 with <M>-elim (aux d1 d2 q1)
        ...| r2 , s2 , q2 rewrite q2 = cong just (sym s2)  

        aux (D-mu d1) (D-mu d2) prf 
          with residual-symmetry-thm (D-mu d1) (D-mu d2) prf
        ...| op , hip with <M>-elim hip
        ...| r , s , q with <M>-elim prf
        ...| rp , refl , qp with aux* d1 d2 qp
        ...| res rewrite q = res

        {-# TERMINATING #-}
        aux* : {n : ℕ}{t : Tel n}{ty : U (suc n)}{k : List (Dμ C t ty)}
             → (d1 d2 : Patchμ t ty) 
             → res d1 d2 ≡ just k
             → forgetμ <M> (res d2 d1) ≡ just (map (↓-map-↓ C-sym) (forgetμ k))
        aux* [] [] prf rewrite sym (just-inj prf) = refl

        aux* (Dμ-A () ∷ _) _ _
        aux* _ (Dμ-A () ∷ _) _

        aux* [] (Dμ-ins x ∷ d2) prf with <M>-elim prf
        ...| s1 , refl , q1 with <M>-elim (aux* [] d2 q1)
        ...| s2 , r2 , q2 rewrite q2 = cong just (cong (_∷_ _) (sym r2))
        aux* (Dμ-ins x ∷ d1) [] prf with <M>-elim prf
        ...| s1 , refl , q1 with <M>-elim (aux* d1 [] q1)
        ...| s2 , r2 , q2 rewrite q2 = cong just (cong (_∷_ _) (sym r2))
        
        aux* [] (Dμ-del x ∷ d2) ()
        aux* [] (Dμ-dwn dx ∷ d2) ()
        aux* (Dμ-del x ∷ d1) [] ()
        aux* (Dμ-dwn dx ∷ d1) [] ()

        aux* (Dμ-ins x ∷ d1) (Dμ-ins y ∷ d2) prf with x ≟-U y | y ≟-U x
        ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
        ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
        ...| yes p | yes _ with <M>-elim prf
        ...| r1 , refl , q1 with <M>-elim (aux* d1 d2 q1)
        ...| r2 , s2 , q2 rewrite q2
           = cong just (subst (λ P → P ++ forgetμ r2 ≡ _) 
                       (sym (forget-cast (gdiff-id y))) 
                       (subst (λ P → forgetμ r2 ≡ map (↓-map-↓ C-sym) (P ++ forgetμ r1)) 
                          (sym (forget-cast (gdiff-id x)))
                          (sym s2)))
        aux* (Dμ-ins x ∷ d1) (Dμ-ins y ∷ d2) prf | no ¬p | no _ 
          with <M>-elim prf
        ...| s1 , refl , q1 with <M>-elim (aux* d1 d2 q1)
        ...| s2 , r2 , q2 rewrite q2 = cong just (cong (_∷_ _) (sym r2))
        

        aux* (Dμ-ins x ∷ d1) (Dμ-del y ∷ d2) prf with <M>-elim prf
        ...| s1 , refl , q1 with <M>-elim (aux* d1 (Dμ-del y ∷ d2) q1)
        ...| s2 , r2 , q2 rewrite q2 = cong just (cong (_∷_ _) (sym r2))
        aux* (Dμ-ins x ∷ d1) (Dμ-dwn dy ∷ d2) prf with <M>-elim prf
        ...| s1 , refl , q1 with <M>-elim (aux* d1 (Dμ-dwn dy ∷ d2) q1)
        ...| s2 , r2 , q2 rewrite q2 = cong just (cong (_∷_ _) (sym r2))

        aux* (Dμ-del x ∷ d1) (Dμ-ins y ∷ d2) prf with <M>-elim prf
        ...| s1 , refl , q1 with <M>-elim (aux* (Dμ-del x ∷ d1) d2 q1)
        ...| s2 , r2 , q2 rewrite q2 = cong just (cong (_∷_ _) (sym r2))
        aux* (Dμ-dwn dx ∷ d1) (Dμ-ins y ∷ d2) prf with <M>-elim prf
        ...| s1 , refl , q1 with <M>-elim (aux* (Dμ-dwn dx ∷ d1) d2 q1)
        ...| s2 , r2 , q2 rewrite q2 = cong just (cong (_∷_ _) (sym r2))


        aux* (Dμ-del x ∷ d1) (Dμ-del y ∷ d2) prf with x ≟-U y | y ≟-U x
        ...| no ¬p | yes p = ⊥-elim (¬p (sym p))
        ...| yes p | no ¬p = ⊥-elim (¬p (sym p))
        aux* (Dμ-del x ∷ d1) (Dμ-del y ∷ d2) () | no ¬p | no ¬p₁
        ...| yes p | yes _ = aux* d1 d2 prf

        aux* (Dμ-del x ∷ d1) (Dμ-dwn dy ∷ d2) prf
         = cool where postulate cool : ∀{a}{A : Set a} → A
        aux* (Dμ-dwn dx ∷ d1) (Dμ-del y ∷ d2) prf
         = cool where postulate cool : ∀{a}{A : Set a} → A
        {-
        aux* (Dμ-del x ∷ d1) (Dμ-dwn dy ∷ d2) prf
          with gapply dy x
        aux* (Dμ-del x ∷ d1) (Dμ-dwn dy ∷ d2) () | nothing
        ...| just x' with <M>-elim prf
        ...| s , refl , q with residualμ-symmetry-thm d1 d2 q
        ...| op , hip with aux* d1 d2 q
        ...| res rewrite hip = cong just (cong (_∷_ _) (just-inj res))
        
        aux* (Dμ-dwn dx ∷ d1) (Dμ-del y ∷ d2) prf
          with gapply dx y
        aux* (Dμ-dwn dx ∷ d1) (Dμ-del y ∷ d2) () | nothing
        ...| just y' with <M>-elim prf
        ...| s1 , refl , q1 with <M>-elim (aux* d1 d2 q1)
        ...| s2 , r2 , q2 rewrite q2 | forget-cast {A = C} dx 
           = cong just (cong (_∷_ _) (sym r2)) 
        -}

        aux* {k = k} (Dμ-dwn dx ∷ d1) (Dμ-dwn dy ∷ d2) prf
          with <M*>-elim-full {f = _∷_ <M> (Dμ-dwn <M> (dx / dy))} {x = res d1 d2}  prf
        ...| (fa , a) , r1 , s1 , q1 with aux* d1 d2 q1
        ...| res with <M>-elim r1
        ...| r2 , s2 , q2 with <M>-elim q2
        ...| r3 , s3 , q3 rewrite s3 with aux dx dy q3
        ...| hip with <M>-elim hip
        ...| r4 , s4 , q4 rewrite q4 | s2 | s1 with <M>-elim res
        ...| r5 , s5 , q5 rewrite q5 
           = cong just (sym (trans (map-++-commute (↓-map-↓ C-sym) (forget r3) (forgetμ a)) 
                       (cong₂ _++_ s4 s5)))
\end{code}

  Now, we havea neat way of relating
  conflicts of symmetric residuals:

\begin{code}
  open import Relation.Binary.PropositionalEquality
\end{code}

%<*conflicts-sym-type>
\begin{code}
  conflicts-sym : {n : ℕ}{t : Tel n}{ty : U n}
                → (d1 d2 : Patch t ty)
                → map (↓-map-↓ C-sym) (conflicts (d1 / d2)) ≡ conflicts (d2 / d1)
\end{code}
%</conflicts-sym-type>
\begin{code}
  conflicts-sym d1 d2 with d1 / d2 | inspect (_/_ d1) d2
  ...| nothing | [ R ] rewrite (residual-nothing d1 d2 R)
     = refl
  ...| just d12 | [ R ] with residual-sym-stable d1 d2 R
  ...| res with <M>-elim res
  ...| r , s , p rewrite p = s
\end{code}
