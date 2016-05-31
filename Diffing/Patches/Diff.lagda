\begin{code}
open import Prelude
open import Diffing.Universe

module Diffing.Patches.Diff where

  open import Diffing.Patches.Diff.D public
  open import Diffing.Patches.Diff.Cost public
\end{code}

        Diffing
  =======================

\begin{code}
  mutual
    {-# TERMINATING #-}
\end{code}
%<*gdiff-def>
\begin{code}
    gdiff : {n : ℕ}{t : T n}{ty : U n} 
          → ElU ty t → ElU ty t → Patch t ty
    gdiff {ty = var} (top a) (top b)    = D-top (gdiff a b)
    gdiff {ty = wk u} (pop a) (pop b)  = D-pop (gdiff a b)
    gdiff {ty = def F x} (red a) (red b) = D-def (gdiff a b)
    gdiff {ty = u1} unit unit = D-unit
    gdiff {ty = ty ⊗ tv} (ay , av) (by , bv) 
      = D-pair (gdiff ay by) (gdiff av bv)
    gdiff {ty = ty ⊕ tv} (inl ay) (inl by) = D-inl (gdiff ay by)
    gdiff {ty = ty ⊕ tv} (inr av) (inr bv) = D-inr (gdiff av bv)
    gdiff {ty = ty ⊕ tv} (inl ay) (inr bv) = D-setl ay bv
    gdiff {ty = ty ⊕ tv} (inr av) (inl by) = D-setr av by
    gdiff {ty = μ ty} a b = D-mu (gdiffL (a ∷ []) (b ∷ []))
\end{code}
%</gdiff-def>

%<*gdiffL-def>
\begin{code}
    gdiffL : {n : ℕ}{t : T n}{ty : U (suc n)} 
           → List (ElU (μ ty) t) → List (ElU (μ ty) t) → Patchμ t ty
    gdiffL [] [] = []
    gdiffL [] (y ∷ ys) with μ-open y
    ...| hdY , chY = Dμ-ins hdY ∷ (gdiffL [] (chY ++ ys)) 
    gdiffL (x ∷ xs) [] with μ-open x
    ...| hdX , chX = Dμ-del hdX ∷ (gdiffL (chX ++ xs) [])
    gdiffL (x ∷ xs) (y ∷ ys) 
      = let
          hdX , chX = μ-open x
          hdY , chY = μ-open y
          d1 = Dμ-ins hdY ∷ (gdiffL (x ∷ xs) (chY ++ ys))
          d2 = Dμ-del hdX ∷ (gdiffL (chX ++ xs) (y ∷ ys))
          d3 = Dμ-dwn (gdiff hdX hdY) ∷ (gdiffL (chX ++ xs) (chY ++ ys))
       in d1 ⊔μ d2 ⊔μ d3
\end{code}
%</gdiffL-def>

       Application
  =========================

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

         Semantics
  ============================

\begin{code}
  D⟦_⟧ : {n : ℕ}{t : T n}{ty : U n}
       → Patch t ty → Maybe (ElU ty t) → Maybe (ElU ty t)
  D⟦ p ⟧ nothing   = nothing
  D⟦ p ⟧ (just el) = gapply p el
\end{code}

           Equality
  ============================

  And finally, we define an extensional equality for patches.

%<*patch-equality>
\begin{code}
  _≡-D_ : {n : ℕ}{t : T n}{ty : U n}
        → Patch t ty → Patch t ty → Set
  d1 ≡-D d2 = ∀ x → gapply d1 x ≡ gapply d2 x
\end{code}
%</patch-equality>

  If we want to calculate with patches, we need some rewrite notion.
  Unfortunately, we can't encode extensional proofs in Agda.
  However, having a proof of (d1 ≡-D d2) is basically having a proof
  that d1 and d2 are the same arrow in the category of versions.

%<*patch-equality-lift>
\begin{code}
  private
    postulate
      ≡-D-lift : {n : ℕ}{t : T n}{ty : U n}{d1 d2 : Patch t ty}
               → d1 ≡-D d2 → d1 ≡ d2
\end{code}
%</patch-equality-lift>

  Now we can substitute over patches.

%<*patch-subst>
\begin{code}
  substP : {n : ℕ}{t : T n}{ty : U n}
         → (P : Patch t ty → Set){d1 d2 : Patch t ty} 
         → d1 ≡-D d2
         → P d1 → P d2
  substP P {d1} {d2} d1≡d2 pd1 with (≡-D-lift {d1 = d1} {d2 = d2} d1≡d2) 
  ...| prf = subst P prf pd1 
\end{code}
%</patch-subst>

  We also make an equality notion for fix-point patches.
  It is also extensional in respect to application, but now,
  also in respect to safeHead. Since that, although gapplyL
  uses a list of ElU (μ ty) t, we are only interested in the head
  of that list, patch equality follows this notion.

%<*patchL-equality>
\begin{code}
  _≡-Dμ_ : {n : ℕ}{t : T n}{ty : U (suc n)}
         → (d1 d2 : Patchμ t ty) → Set
  d1 ≡-Dμ d2 = ∀ x → gapplyL d1 x ≡ gapplyL d2 x
\end{code}
%</patchL-equality>

  This postulate is fairly dangerous. It does introduce a decent amount of contradictions.
  Yet, we need this to be able to prove some sort of behavioural equivalence of patches.
  Or, at least, to make the proof easier. We justify this postulate as follows:

    safeHead x ≡ safeHead y iff (x ≡ y ≡ [ z ] ∨ Disagree x y)

  If x and y are the same singleton list, than they are indeed equal!
  
  If they disagree, however, it is more complicated. We define Disagree as follows:

    Disagree x y ≜ safeHead x ≡ safeHead y ≡ nothing

  It doesn't really matter what x and y are. Let's imagine a patch with a hole
  P[]. Since gapply (D-mu x) e ≡ gapplyL x (e ∷ []) >>= safeHead ≡ nothing (and similarly for y)
  we have that gapply P[x] ≡ gapply P[y] ≡ nothing. This means that although x and y are
  propositionally different, in the context of patches they are both not defined for e,
  therefore they are NOT arrows in the patch category of e.

%<*patchL-equality-lift>
\begin{code}
  private
    postulate
      ≡-Dμ-lift : {n : ℕ}{t : T n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                → d1 ≡-Dμ d2 → d1 ≡ d2

  substPμ : {n : ℕ}{t : T n}{ty : U (suc n)}
          → (P : Patchμ t ty → Set){d1 d2 : Patchμ t ty} 
          → d1 ≡-Dμ d2
          → P d1 → P d2
  substPμ P {d1} {d2} d1≡d2 pd1 with (≡-Dμ-lift {d1 = d1} {d2 = d2} d1≡d2) 
  ...| prf = subst P prf pd1 

  congPμ : {A : Set}{n : ℕ}{t : T n}{ty : U (suc n)}
         → (P : Patchμ t ty → A) {d1 d2 : Patchμ t ty}
         → d1 ≡-Dμ d2 → P d1 ≡ P d2
  congPμ p {d1} {d2} hip = substPμ (λ Q → p Q ≡ p d2) (λ x → sym (hip x)) refl

  open import Data.Nat.Properties

  ⊔μ-≡ : {n : ℕ}{t : T n}{ty : U (suc n)}
           (a1 a2 : Patchμ t ty)
           {b1 b2 : Patchμ t ty}
         → a1 ≡-Dμ b1
         → a2 ≡-Dμ b2
         → (a1 ⊔μ a2) ≡-Dμ (b1 ⊔μ b2)
  ⊔μ-≡ a1 a2 {b1} {b2} p1 p2
    rewrite (≡-Dμ-lift {d1 = a1} {d2 = b1} p1) 
          | (≡-Dμ-lift {d1 = a2} {d2 = b2} p2)
          = λ x → refl
\end{code}
%</patchL-equality-lift>

