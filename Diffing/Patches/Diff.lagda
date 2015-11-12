\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils

module Diffing.Patches.Diff where
\end{code}

%<*ValU>
\begin{code}
  ValU : {n : ℕ} → U (suc n) → Tel n → Set
  ValU ty t = ElU ty (tcons u1 t)
\end{code}
%</ValU>

%<*D-def>
\begin{code}
  mutual
    data D : {n : ℕ} → Tel n → U n → Set where
      D-void : {n : ℕ}{t : Tel n} → D t u1
      D-inl  : {n : ℕ}{t : Tel n}{a b : U n} 
             → D t a → D t (a ⊕ b)
      D-inr  : {n : ℕ}{t : Tel n}{a b : U n} 
             → D t b → D t (a ⊕ b)
      D-setl  : {n : ℕ}{t : Tel n}{a b : U n} 
              → ElU a t → ElU b t → D t (a ⊕ b)
      D-setr  : {n : ℕ}{t : Tel n}{a b : U n} 
              → ElU b t → ElU a t → D t (a ⊕ b)
      D-pair : {n : ℕ}{t : Tel n}{a b : U n} 
             → D t a → D t b → D t (a ⊗ b)
      D-mu : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → List (Dμ t a) → D t (μ a)
      D-β : {n : ℕ}{t : Tel n}{F : U (suc n)}{x : U n} 
          → D (tcons x t) F → D t (β F x)
      D-top : {n : ℕ}{t : Tel n}{a : U n}
            → D t a → D (tcons a t) vl
      D-pop : {n : ℕ}{t : Tel n}{a b : U n}
            → D t b → D (tcons a t) (wk b)
      -- _∘ᴰ_  : {n : ℕ}{t : Tel n}{a : U n}
      --      → D t a → D t a → D t a
      D-id  : {n : ℕ}{t : Tel n}{a : U n}
            → D t a

    data Dμ : {n : ℕ} → Tel n → U (suc n) → Set where
      Dμ-ins : {n : ℕ}{t : Tel n}{a : U (suc n)} → ValU a t → Dμ t a
      Dμ-del : {n : ℕ}{t : Tel n}{a : U (suc n)} → ValU a t → Dμ t a
      Dμ-cpy : {n : ℕ}{t : Tel n}{a : U (suc n)} → ValU a t → Dμ t a
      Dμ-dwn : {n : ℕ}{t : Tel n}{a : U (suc n)} → D t (β a u1) → Dμ t a
\end{code}
%</D-def>

  The cost function is trivial for the non-inductive types.
  The inductive types are a bit trickier, though.
  We want our diff to have maximum sharing, that means
  we seek to copy most of the information we see.
  However, there are two obvious ways of copying:

    (D-mu-cpy x d) ∨ (D-mu-down (diff x x) d)

  We want the first one to be chosen.
  Which means, 
  
    cost (D-mu-cpy x d) < cost (D-mu-down (diff x x) d)
  ↔         k + cost d  < cost (diff x x) + 1 + cost d
  ⇐                  k  < cost (diff x x) + 1
  
  However, diff x x will basically be copying every constructor of x,
  which is intuitively the size of x. We then define the cost of
  copying x as the size of x.

  Inserting and deleting, on the other hand, must be more
  expensive than making structural changes (when possible!)
  The same reasoning applies to the fact that we prefer copying
  over inserting and deleting.

    D-mu-cpy x d ≈ D-mu-down (diff x x) d ≈ D-mu-ins x (D-mu-del x d)
  
  With this in mind, we implement the cost function as follows:

\begin{code}
  mutual
\end{code}
%<*cost-def>
\begin{code}
    cost : {n : ℕ}{t : Tel n}{ty : U n} → D t ty → ℕ
    cost  D-void        = 1
    cost (D-inl d)      = cost d
    cost (D-inr d)      = cost d
    cost (D-setl _ _)   = 1
    cost (D-setr _ _)   = 1
    cost (D-pair da db) = cost da + cost db
    cost (D-β d)   = cost d
    cost (D-top d) = cost d
    cost (D-pop d) = cost d
    -- cost (x ∘ᴰ y)  = cost x + cost y
    cost D-id      = 0
    cost (D-mu l)  = sum-cost l
      where
        sum-cost : {n : ℕ}{t : Tel n}{ty : U (suc n)} → List (Dμ t ty) → ℕ
        sum-cost [] = 0
        sum-cost (x ∷ l) = costμ x + sum-cost l

    costμ : {n : ℕ}{t : Tel n}{ty : U (suc n)} → Dμ t ty → ℕ
    costμ (Dμ-ins x) = sizeElU x + 1
    costμ (Dμ-del x) = sizeElU x + 1
    costμ (Dμ-cpy x) = sizeElU x
    costμ (Dμ-dwn x) = cost x
\end{code}
%</cost-def>

%<*lub-def>
\begin{code}
  _⊔_ : {n : ℕ}{t : Tel n}{ty : U n}
      → D t ty → D t ty → D t ty
  _⊔_ {ty = ty} da db with cost da ≤?-ℕ cost db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lub-def>

%<*lubmu-def>
\begin{code}
  _⊔μ_ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
      → List (Dμ t ty) → List (Dμ t ty) → List (Dμ t ty)
  _⊔μ_ {ty = ty} da db with cost (D-mu da) ≤?-ℕ cost (D-mu db)
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lubmu-def>

        Diffing
  =======================

\begin{code}
  infixr 20 _⊔_
  infixr 20 _⊔μ_
  mutual
\end{code}
%<*gdiff-def>
\begin{code}
    {-# TERMINATING #-}
    gdiff : {n : ℕ}{t : Tel n}{ty : U n} 
          → ElU ty t → ElU ty t → D t ty
    gdiff {ty = vl} (top a) (top b)    = D-top (gdiff a b)
    gdiff {ty = wk u} (pop a) (pop b)  = D-pop (gdiff a b)
    gdiff {ty = β F x} (red a) (red b) = D-β (gdiff a b)

    -- Units and products are trivial.
    gdiff {ty = u1} void void = D-void
    gdiff {ty = ty ⊗ tv} (ay , av) (by , bv) 
      = D-pair (gdiff ay by) (gdiff av bv)

    -- Coproducts are not very hard either
    gdiff {ty = ty ⊕ tv} (inl ay) (inl by) = D-inl (gdiff ay by)
    gdiff {ty = ty ⊕ tv} (inr av) (inr bv) = D-inr (gdiff av bv)
    gdiff {ty = ty ⊕ tv} (inl ay) (inr bv) = D-setl ay bv
    gdiff {ty = ty ⊕ tv} (inr av) (inl by) = D-setr av by

    -- Now we get to the interesting bit.
    -- Note that we need to use lists to handle
    -- the possibility of multiple arguments.
    gdiff {ty = μ ty} a b = D-mu (gdiffL (a ∷ []) (b ∷ []))
\end{code}
%</gdiff-def>

%<*gdiffL-def>
\begin{code}
    gdiffL : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
           → List (ElU (μ ty) t) → List (ElU (μ ty) t) → List (Dμ t ty)
    gdiffL [] [] = []
    gdiffL [] (y ∷ ys) with μ-open y
    ...| hdY , chY = Dμ-ins hdY ∷ (gdiffL [] (chY ++ ys)) 
    gdiffL (x ∷ xs) [] with μ-open x
    ...| hdX , chX = Dμ-del hdX ∷ (gdiffL (chX ++ xs) [])
    gdiffL (x ∷ xs) (y ∷ ys) with μ-open x | μ-open y
    ...| hdX , chX | hdY , chY with hdX ≟-U hdY
    ...| no  _ = let
          d1 = Dμ-ins hdY ∷ (gdiffL (x ∷ xs) (chY ++ ys))
          d2 = Dμ-del hdX ∷ (gdiffL (chX ++ xs) (y ∷ ys))
          d3 = Dμ-dwn (gdiff (red hdX) (red hdY)) ∷ (gdiffL (chX ++ xs) (chY ++ ys))
       in d1 ⊔μ d2 ⊔μ d3
    ...|  yes _ = let
          -- d1 = D-mu-ins hdY (gdiffL (x ∷ xs) (chY ++ ys))
          -- d2 = D-mu-del hdX (gdiffL (chX ++ xs) (y ∷ ys))
          d3 = Dμ-cpy hdX ∷ (gdiffL (chX ++ xs) (chY ++ ys))
       in d3
\end{code}
%</gdiffL-def>

       Application
  =========================

\begin{code}
  open import Diffing.Utils.Monads
  open Monad {{...}}

  mutual
\end{code}
%<*gapply-def>
\begin{code}
    gapply : {n : ℕ}{t : Tel n}{ty : U n}
           → D t ty → ElU ty t → Maybe (ElU ty t)
    gapply D-id   el   = just el
    gapply D-void void = just void

    gapply (D-inl diff) (inl el) = inl <$>+1 gapply diff el
    gapply (D-inl diff) (inr el) = nothing

    gapply (D-inr diff) (inl el) = nothing
    gapply (D-inr diff) (inr el) = inr <$>+1 gapply diff el

    gapply (D-setl x y) (inl el) with x ≟-U el
    ...| yes _ = just (inr y)
    ...| no  _ = nothing
    gapply (D-setl _ _) (inr _) = nothing

    gapply (D-setr y x) (inr el) with y ≟-U el
    ...| yes _ = just (inl x)
    ...| no  _ = nothing
    gapply (D-setr _ _) (inl _) = nothing

    gapply (D-pair da db) (a , b) with gapply da a
    ...| nothing = nothing
    ...| just ra = _,_ ra <$>+1 gapply db b

    gapply (D-β diff) (red el) = red <$>+1 gapply diff el
    gapply (D-top diff) (top el) = top <$>+1 gapply diff el
    gapply (D-pop diff) (pop el) = pop <$>+1 gapply diff el

    -- gapply (dx ∘ᴰ dy) el = gapply dy el >>= gapply dx

    gapply {ty = μ ty} (D-mu d) el = gapplyL d (el ∷ []) >>= safeHead
\end{code}
%</gapply-def>

%<*safeHead-def>
\begin{code}
    safeHead : ∀{a}{A : Set a} → List A → Maybe A
    safeHead []      = nothing
    safeHead (x ∷ _) = just x
\end{code}
%</safeHead-def>

%<*gIns-def>
\begin{code}
    gIns : {n : ℕ}{t : Tel n}{ty : U (suc n)}
         → ElU ty (tcons u1 t) → List (ElU (μ ty) t) → Maybe (List (ElU (μ ty) t))
    gIns x l with μ-close (x , l)
    ...| nothing = nothing
    ...| just (r , l') = just (r ∷ l')
\end{code}
%</gIns-def>

%<*gDel-def>
\begin{code}
    gDel : {n : ℕ}{t : Tel n}{ty : U (suc n)}
         → ElU ty (tcons u1 t) → List (ElU (μ ty) t) → Maybe (List (ElU (μ ty) t))
    gDel x [] = nothing
    gDel {ty = ty} x (y ∷ ys) with μ-open y
    ...| hdY , chY with x ≟-U hdY
    ...| yes _ = just (chY ++ ys)
    ...| no  _ = nothing
\end{code}
%</gDel-def>

%<*gapplyL-def>
\begin{code}
    gapplyL : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            → List (Dμ t ty) → List (ElU (μ ty) t) → Maybe (List (ElU (μ ty) t))
    gapplyL [] l = just l
    gapplyL (Dμ-ins x  ∷ d) l = gapplyL d l >>= gIns x
    gapplyL (Dμ-del x  ∷ d) l = gDel x l    >>= gapplyL d 
    gapplyL (Dμ-cpy x  ∷ d) l = gDel x l    >>= gapplyL d >>= gIns x
    gapplyL (Dμ-dwn dx ∷ d) [] = nothing
    gapplyL (Dμ-dwn dx ∷ d) (y ∷ l) with μ-open y
    ...| hdY , chY with gapply dx (red hdY)
    ...| nothing       = nothing
    ...| just (red y') = gapplyL d (chY ++ l) >>= gIns y' 
\end{code}
%</gapplyL-def>

           Equality
  ============================

  And finally, we define an extensional equality for patches.

%<*patch-equality>
\begin{code}
  _≡-D_ : {n : ℕ}{t : Tel n}{ty : U n}
        → D t ty → D t ty → Set
  d1 ≡-D d2 = ∀ x → gapply d1 x ≡ gapply d2 x
\end{code}
%</patch-equality>

  Plus, it is fairly usefull to have some sort of equality
  over Maybe monad.

%<*patchM-equality>
\begin{code}
  _≡-DM_ : {n : ℕ}{t : Tel n}{ty : U n}
        → Maybe (D t ty) → Maybe (D t ty) → Set
  nothing   ≡-DM nothing   = Unit
  (just d1) ≡-DM (just d2) = d1 ≡-D d2
  _         ≡-DM _         = ⊥
\end{code}
%</patchM-equality>

  If we want to calculate with patches, we need some rewrite notion.
  Unfortunately, we can't encode extensional proofs in Agda.
  However, having a proof of (d1 ≡-D d2) is basically having a proof
  that d1 and d2 are the same arrow in the category of versions.

%<*patch-equality-lift>
\begin{code}
  postulate
    ≡-D-lift : {n : ℕ}{t : Tel n}{ty : U n}{d1 d2 : D t ty}
             → d1 ≡-D d2 → d1 ≡ d2
\end{code}
%</patch-equality-lift>

  Now we can substitute over patches.

%<*patch-subst>
\begin{code}
  substP : {n : ℕ}{t : Tel n}{ty : U n}
         → (P : D t ty → Set){d1 d2 : D t ty} 
         → d1 ≡-D d2
         → P d1 → P d2
  substP P {d1} {d2} d1≡d2 pd1 with (≡-D-lift {d1 = d1} {d2 = d2} d1≡d2) 
  ...| prf = subst P prf pd1 
\end{code}
%</patch-subst>