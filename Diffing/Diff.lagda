\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils

module Diffing.Diff where
\end{code}

%<*D-def>
\begin{code}
  data D : {n : ℕ} → Tel n → U n → Set where
    D-void : {n : ℕ}{t : Tel n} → D t u1
    D-inl  : {n : ℕ}{t : Tel n}{a b : U n} 
           → D t a → D t (a ⊕ b)
    D-inr  : {n : ℕ}{t : Tel n}{a b : U n} 
           → D t b → D t (a ⊕ b)
    D-set  : {n : ℕ}{t : Tel n}{a b : U n} 
           → ElU a t → ElU b t → D t (a ⊕ b)
    D-pair : {n : ℕ}{t : Tel n}{a b : U n} 
           → D t a → D t b → D t (a ⊗ b)
    D-mu-end : {n : ℕ}{t : Tel n}{a : U (suc n)} 
             → D t (μ a)
    D-mu-cpy : {n : ℕ}{t : Tel n}{a : U (suc n)} 
             → ElU a (tcons u1 t) → D t (μ a) → D t (μ a)
    D-mu-ins : {n : ℕ}{t : Tel n}{a : U (suc n)} 
             → ElU a (tcons u1 t) → D t (μ a) → D t (μ a)
    D-mu-del : {n : ℕ}{t : Tel n}{a : U (suc n)} 
             → ElU a (tcons u1 t) → D t (μ a) → D t (μ a)
    D-mu-down : {n : ℕ}{t : Tel n}{a : U (suc n)} 
              → D t (β a u1) → D t (μ a) → D t (μ a)
    D-β : {n : ℕ}{t : Tel n}{F : U (suc n)}{x : U n} 
        → D (tcons x t) F → D t (β F x)
    D-top : {n : ℕ}{t : Tel n}{a : U n}
          → D t a → D (tcons a t) vl
    D-pop : {n : ℕ}{t : Tel n}{a b : U n}
          → D t b → D (tcons a t) (wk b)
\end{code}
%</D-def>

%<*cost-def>
\begin{code}
  cost : {n : ℕ}{t : Tel n}{ty : U n} → D t ty → ℕ
  cost {n} D-void = n
  cost {n} (D-inl d) = cost d
  cost {n} (D-inr d) = cost d
  cost {n} (D-set _ _) = n
  cost {n} (D-pair d d₁) = cost d + cost d₁
  cost {n} D-mu-end = 0
  cost {n} (D-mu-cpy x d) = n + cost d
  cost {n} (D-mu-ins x d) = 2 * n + cost d
  cost {n} (D-mu-del x d) = 2 * n + cost d
  cost {n} (D-mu-down d d₁) = cost d + cost d₁
  cost {n} (D-β d) = cost d
  cost {suc n} (D-top d) = cost d
  cost {suc n} (D-pop d) = cost d
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

\begin{code}
  infixr 20 _⊔_
\end{code}

\begin{code}
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
    gdiff {ty = ty ⊕ tv} (inl ay) (inr bv) = D-set ay bv
    gdiff {ty = ty ⊕ tv} (inr av) (inl by) = D-set by av

    -- Now we get to the interesting bit.
    -- Note that we need to use lists to handle
    -- the possibility of multiple arguments.
    gdiff {ty = μ ty} a b = gdiffL (a ∷ []) (b ∷ [])
\end{code}
%</gdiff-def>

%<*gdiffL-def>
\begin{code}
    gdiffL : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
           → List (ElU (μ ty) t) → List (ElU (μ ty) t) → D t (μ ty)
    gdiffL [] [] = D-mu-end
    gdiffL [] (y ∷ ys) with μ-open y
    ...| hdY , chY = D-mu-ins hdY (gdiffL [] (chY ++ ys)) 
    gdiffL (x ∷ xs) [] with μ-open x
    ...| hdX , chX = D-mu-del hdX (gdiffL (chX ++ xs) [])
    gdiffL (x ∷ xs) (y ∷ ys) with μ-open x | μ-open y
    ...| hdX , chX | hdY , chY with hdX ≟-U hdY
    ...| no  _ = let
          d1 = D-mu-ins hdY (gdiffL (x ∷ xs) (chY ++ ys))
          d2 = D-mu-del hdX (gdiffL (chX ++ xs) (y ∷ ys))
          d3 = D-mu-down (gdiff (red hdX) (red hdY)) (gdiffL (chX ++ xs) (chY ++ ys))
       in d1 ⊔ d2 ⊔ d3
    ...|  yes _ = let
          -- d1 = D-mu-ins hdY (gdiffL (x ∷ xs) (chY ++ ys))
          -- d2 = D-mu-del hdX (gdiffL (chX ++ xs) (y ∷ ys))
          d3 = D-mu-cpy hdX (gdiffL (chX ++ xs) (chY ++ ys))
       in d3
\end{code}
%</gdiffL-def>

\begin{code}
  open import Diffing.Utils.Monads
  open Monad {{...}}

  mutual
\end{code}

%<*gapply-def>
\begin{code}
    gapply : {n : ℕ}{t : Tel n}{ty : U n}
           → D t ty → ElU ty t → Maybe (ElU ty t)
    gapply D-void void = just void

    gapply (D-inl diff) (inl el) = inl <$>+1 gapply diff el
    gapply (D-inl diff) (inr el) = nothing

    gapply (D-inr diff) (inl el) = nothing
    gapply (D-inr diff) (inr el) = inr <$>+1 gapply diff el

    gapply (D-set x y) (inl el) with x ≟-U el
    ...| yes _ = just (inr y)
    ...| no  _ = nothing

    gapply (D-set x y) (inr el) with y ≟-U el
    ...| yes _ = just (inl x)
    ...| no  _ = nothing

    gapply (D-pair da db) (a , b) with gapply da a
    ...| nothing = nothing
    ...| just ra = _,_ ra <$>+1 gapply db b

    gapply (D-β diff) (red el) = red <$>+1 gapply diff el
    gapply (D-top diff) (top el) = top <$>+1 gapply diff el
    gapply (D-pop diff) (pop el) = pop <$>+1 gapply diff el

    gapply {ty = μ ty} d el = gapplyL d (el ∷ []) >>= safeHead
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
            → D t (μ ty) → List (ElU (μ ty) t) → Maybe (List (ElU (μ ty) t))
    gapplyL D-mu-end l = just l
    gapplyL (D-mu-ins x d) l = gapplyL d l >>= gIns x
    gapplyL (D-mu-del x d) l = gDel x l    >>= gapplyL d 
    gapplyL (D-mu-cpy x d) l = gDel x l    >>= gapplyL d >>= gIns x
    gapplyL (D-mu-down x d) [] = nothing
    gapplyL (D-mu-down (D-β x) d) (y ∷ l) with μ-open y
    ...| hdY , chY with gapply x hdY
    ...| nothing = nothing
    ...| just y' = gapplyL d (chY ++ l) >>= gIns y' 
\end{code}
%</gapplyL-def>
  
