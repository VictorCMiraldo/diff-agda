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
    data D {a}(A : {n : ℕ} → Tel n → U n → Set a) : {n : ℕ} → Tel n → U n → Set a where
      D-A    : {n : ℕ}{t : Tel n}{ty : U n} → A t ty → D A t ty

      D-id : {n : ℕ}{t : Tel n}{ty : U n} → D A t ty

      D-void : {n : ℕ}{t : Tel n} → D A t u1
      D-inl  : {n : ℕ}{t : Tel n}{a b : U n} 
             → D A t a → D A t (a ⊕ b)
      D-inr  : {n : ℕ}{t : Tel n}{a b : U n} 
             → D A t b → D A t (a ⊕ b)
      D-setl  : {n : ℕ}{t : Tel n}{a b : U n} 
              → ElU a t → ElU b t → D A t (a ⊕ b)
      D-setr  : {n : ℕ}{t : Tel n}{a b : U n} 
              → ElU b t → ElU a t → D A t (a ⊕ b)
      D-pair : {n : ℕ}{t : Tel n}{a b : U n} 
             → D A t a → D A t b → D A t (a ⊗ b)
      D-mu : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → List (Dμ A t a) → D A t (μ a)
      D-β : {n : ℕ}{t : Tel n}{F : U (suc n)}{x : U n} 
          → D A (tcons x t) F → D A t (β F x)
      D-top : {n : ℕ}{t : Tel n}{a : U n}
            → D A t a → D A (tcons a t) vl
      D-pop : {n : ℕ}{t : Tel n}{a b : U n}
            → D A t b → D A (tcons a t) (wk b)
      -- _∘ᴰ_  : {n : ℕ}{t : Tel n}{a : U n}
      --      → D t a → D t a → D t a
      -- D-id  : {n : ℕ}{t : Tel n}{a : U n}
      --      → D t a

    data Dμ {a}(A : {n : ℕ} → Tel n → U n → Set a) : {n : ℕ} → Tel n → U (suc n) → Set a where
      Dμ-A   : {n : ℕ}{t : Tel n}{a : U (suc n)} → A t (μ a) → Dμ A t a
      Dμ-ins : {n : ℕ}{t : Tel n}{a : U (suc n)} → ValU a t → Dμ A t a
      Dμ-del : {n : ℕ}{t : Tel n}{a : U (suc n)} → ValU a t → Dμ A t a
      Dμ-cpy : {n : ℕ}{t : Tel n}{a : U (suc n)} → ValU a t → Dμ A t a
      Dμ-dwn : {n : ℕ}{t : Tel n}{a : U (suc n)} → ValU a t → D A t (β a u1) → Dμ A t a
\end{code}
%</D-def>

%<*Patch-def>
\begin{code}
  Patch : {n : ℕ} → Tel n → U n → Set
  Patch t ty = D (const (const ⊥)) t ty
       
  Patchμ : {n : ℕ} → Tel n → U (suc n) → Set
  Patchμ t ty = List (Dμ (const (const ⊥)) t ty)
\end{code}
%</Patch-def>

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
    cost : {n : ℕ}{t : Tel n}{ty : U n} → Patch t ty → ℕ
    cost (D-A ())
    cost D-id           = 0
    cost  D-void        = 1
    cost (D-inl d)      = cost d
    cost (D-inr d)      = cost d
    cost (D-setl _ _)   = 1
    cost (D-setr _ _)   = 1
    cost (D-pair da db) = cost da + cost db
    cost (D-β d)   = cost d
    cost (D-top d) = cost d
    cost (D-pop d) = cost d
    cost (D-mu l)  = sum-cost l
      where
        sum-cost : {n : ℕ}{t : Tel n}{ty : U (suc n)} → Patchμ t ty → ℕ
        sum-cost [] = 0
        sum-cost (x ∷ l) = costμ x + sum-cost l

    costμ : {n : ℕ}{t : Tel n}{ty : U (suc n)} → Dμ (const (const ⊥)) t ty → ℕ
    costμ (Dμ-A ())
    costμ (Dμ-ins x) = sizeElU x + 1
    costμ (Dμ-del x) = sizeElU x + 1
    costμ (Dμ-cpy x) = sizeElU x
    costμ (Dμ-dwn _ x) = cost x
\end{code}
%</cost-def>

%<*lub-def>
\begin{code}
  _⊔_ : {n : ℕ}{t : Tel n}{ty : U n}
      → Patch t ty → Patch t ty → Patch t ty
  _⊔_ {ty = ty} da db with cost da ≤?-ℕ cost db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lub-def>

%<*lubmu-def>
\begin{code}
  _⊔μ_ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
      → Patchμ t ty → Patchμ t ty → Patchμ t ty
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
          → ElU ty t → ElU ty t → Patch t ty
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
           → List (ElU (μ ty) t) → List (ElU (μ ty) t) → Patchμ t ty
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
          d3 = Dμ-dwn hdX (gdiff (red hdX) (red hdY)) ∷ (gdiffL (chX ++ xs) (chY ++ ys))
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
           → Patch t ty → ElU ty t → Maybe (ElU ty t)
    gapply (D-A ())

    gapply D-id x = just x

    gapply D-void void = just void

    gapply (D-inl diff) (inl el) = inl <M> gapply diff el
    gapply (D-inl diff) (inr el) = nothing

    gapply (D-inr diff) (inl el) = nothing
    gapply (D-inr diff) (inr el) = inr <M> gapply diff el

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
    ...| just ra = _,_ ra <M> gapply db b

    gapply (D-β diff) (red el) = red <M> gapply diff el
    gapply (D-top diff) (top el) = top <M> gapply diff el
    gapply (D-pop diff) (pop el) = pop <M> gapply diff el

    -- gapply (dx ∘ᴰ dy) el = gapply dy el >>= gapply dx

    gapply {ty = μ ty} (D-mu d) el = gapplyL d (el ∷ []) >>= safeHead
\end{code}
%</gapply-def>

%<*safeHead-def>
\begin{code}
    safeHead : ∀{a}{A : Set a} → List A → Maybe A
    safeHead []       = nothing
    safeHead (x ∷ []) = just x
    safeHead _        = nothing
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
            → Patchμ t ty → List (ElU (μ ty) t) → Maybe (List (ElU (μ ty) t))
    gapplyL [] [] = just []
    gapplyL [] _  = nothing
    gapplyL (Dμ-A () ∷ _)
    gapplyL (Dμ-ins x  ∷ d) l = gapplyL d l >>= gIns x
    gapplyL (Dμ-del x  ∷ d) l = gDel x l    >>= gapplyL d 
    gapplyL (Dμ-cpy x  ∷ d) l = gDel x l    >>= gapplyL d >>= gIns x
    gapplyL (Dμ-dwn _ dx ∷ d) [] = nothing
    gapplyL (Dμ-dwn x dx ∷ d) (y ∷ l) with μ-open y
    ...| hdY , chY with x ≟-U hdY
    ...| no  x≢y = nothing
    ...| yes x≡y with gapply dx (red hdY)
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
      ≡-D-lift : {n : ℕ}{t : Tel n}{ty : U n}{d1 d2 : Patch t ty}
               → d1 ≡-D d2 → d1 ≡ d2
\end{code}
%</patch-equality-lift>

  Now we can substitute over patches.

%<*patch-subst>
\begin{code}
  substP : {n : ℕ}{t : Tel n}{ty : U n}
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
  _≡-Dμ_ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
         → (d1 d2 : Patchμ t ty) → Set
  d1 ≡-Dμ d2 = ∀ x → (gapplyL d1 x >>= safeHead)
                   ≡ (gapplyL d2 x >>= safeHead)
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
      ≡-Dμ-lift : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                → d1 ≡-Dμ d2 → d1 ≡ d2
\end{code}
%</patchL-equality-lift>

   Normalization
   =============

%<*NF-def>
\begin{code}
  NF* : {n : ℕ}{t : Tel n}{ty : U (suc n)} → Patchμ t ty → Set
  NF* [] = Unit
  NF* (Dμ-ins _ ∷ ds) = NF* ds
  NF* (Dμ-del _ ∷ ds) = NF* ds
  NF* (_ ∷ _) = ⊥

  NF : {n : ℕ}{t : Tel n}{ty : U n} → Patch t ty → Set
  NF (D-mu xs) = NF* xs
  NF (D-β d)   = NF d
  NF (D-inl d) = NF d
  NF (D-inr d) = NF d
  NF (D-top d) = NF d
  NF (D-pop d) = NF d
  NF (D-pair da db) = NF da × NF db
  NF _ = Unit
\end{code}
%</NF-def>

  Note that after normalization our patch language becomes extremely
  close to the LDEnd, LDIns, LDDel thing. It is the Dμ-dwn
  constructor that pushes us to that next level where
  we can track differences recursively.

\begin{code}
  mutual
\end{code}
%<*normalize-type>
\begin{code}
    normalize : {n : ℕ}{t : Tel n}{ty : U n} → Patch t ty → Σ (Patch t ty) NF
\end{code}
%</normalize-type>
\begin{code}
    normalize (D-A ())
    normalize D-id   = D-id , unit
    normalize D-void = D-void , unit
    normalize (D-inl d) with normalize d
    ...| nfd , prf = D-inl nfd , prf
    normalize (D-inr d) with normalize d
    ...| nfd , prf = D-inr nfd , prf
    normalize (D-setl x y) = D-setl x y , unit
    normalize (D-setr x y) = D-setr x y , unit
    normalize (D-pair d e) with normalize d | normalize e
    ...| nfd , prfd | nfe , prfe = (D-pair nfd nfe) , (prfd , prfe)
    normalize (D-β d) with normalize d
    ...| nfd , prf = (D-β nfd) , prf
    normalize (D-top d) with normalize d
    ...| nfd , prf = D-top nfd , prf
    normalize (D-pop d) with normalize d
    ...| nfd , prf = D-pop nfd , prf
    normalize (D-mu xs) with normalize* xs
    ...| ns , prf = D-mu ns , prf
    

    normalize* : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
                 → Patchμ t ty → Σ (Patchμ t ty) NF*
    normalize* [] = [] , unit
    normalize* (Dμ-A () ∷ _)
    normalize* (Dμ-ins x ∷ xs) with normalize* xs
    ...| ns , prf = Dμ-ins x ∷ ns , prf
    normalize* (Dμ-del x ∷ xs) with normalize* xs
    ...| ns , prf = Dμ-del x ∷ ns , prf
    normalize* (Dμ-dwn x dx ∷ xs) with gapply dx (red x)
    ...| nothing = [] , unit
    ...| just (red y) with normalize* xs
    ...| ns , prf = Dμ-del x ∷ Dμ-ins y ∷ ns , prf
    normalize* (Dμ-cpy x ∷ xs) with normalize* xs
    ...| ns , prf = Dμ-del x ∷ Dμ-ins x ∷ ns , prf
\end{code}

\begin{code}
  nf : {n : ℕ}{t : Tel n}{ty : U n} → Patch t ty → Patch t ty
  nf p = p1 (normalize p)

  nf-prf : {n : ℕ}{t : Tel n}{ty : U n}(p : Patch t ty) → NF (nf p)
  nf-prf p = p2 (normalize p)
\end{code}

  Normalization is correct, with respect to observational equality over patches
  for fixed points.

%<*nf-correct-type>
\begin{code}
  nf-correct : {n : ℕ}{t : Tel n}{ty : U n}(p : Patch t ty)
             → p ≡-D nf p
\end{code}
%</nf-correct-type>
\begin{code}
  nf-correct (D-A ()) _
  nf-correct D-id x            = refl
  nf-correct D-void void       = refl
  nf-correct (D-inl p) (inl el)
    rewrite nf-correct p el = refl
  nf-correct (D-inl p) (inr el) = refl
  nf-correct (D-inr p) (inl el) = refl
  nf-correct (D-inr p) (inr el)
    rewrite nf-correct p el = refl
  nf-correct (D-setl x x₁) el  = refl
  nf-correct (D-setr x x₁) el  = refl
  nf-correct (D-pair pa pb) (ela , elb)
    rewrite sym (nf-correct pa ela) with gapply pa ela
  ...| nothing = refl
  ...| just a' rewrite nf-correct pb elb = refl
  nf-correct (D-β p) (red el) 
    rewrite nf-correct p el = refl
  nf-correct (D-top p) (top el)
    rewrite nf-correct p el = refl
  nf-correct (D-pop p) (pop el)
    rewrite nf-correct p el = refl
  nf-correct (D-mu x) el 
    = aux x (el ∷ [])
    where
      open import Relation.Binary.PropositionalEquality

      aux : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            (ps : Patchμ t ty)
          → ps ≡-Dμ p1 (normalize* ps)
      aux [] es = refl

      aux (Dμ-A () ∷ _)

      aux (Dμ-ins x ∷ ps) es with ≡-Dμ-lift {d1 = ps} {d2 = p1 (normalize* ps)} (aux ps)
      ...| r = cong (λ P → gapplyL P es >>= gIns x >>= safeHead) r

      aux (Dμ-del x ∷ ps) [] = refl
      aux (Dμ-del x ∷ ps) (e ∷ es) with μ-open e
      ...| hdE , chE with x ≟-U hdE
      ...| no  x≢e = refl
      ...| yes x≡e = aux ps (chE ++ es)

      aux (Dμ-cpy x ∷ ps) [] = refl
      aux (Dμ-cpy x ∷ ps) (e ∷ es) with μ-open e
      ...| hdE , chE with x ≟-U hdE
      ...| no  x≢e = refl
      ...| yes x≡e = cong (λ P → gapplyL P (chE ++ es) >>= gIns x >>= safeHead) 
                          (≡-Dμ-lift {d1 = ps} {d2 = p1 (normalize* ps)} (aux ps))

      aux (Dμ-dwn x dx ∷ ps) [] 
        with gapply dx (red x)
      ...| nothing = refl
      ...| just (red x') = refl
      aux (Dμ-dwn x dx ∷ ps) (e ∷ es) 
        with μ-open e | inspect μ-open e
      ...| hdE , chE | [ R ] with x ≟-U hdE | inspect (_≟-U_ x) hdE
      ...| no  x≢e | [ R2 ] with gapply dx (red x)
      aux (Dμ-dwn x dx ∷ ps) (e ∷ es) | hdE , chE | [ R ] 
          | no x≢e   | [ R2 ] | nothing = refl
      aux (Dμ-dwn x dx ∷ ps) (e ∷ es) | hdE , chE | [ R ] 
          | no x≢e   | [ R2 ] | just (red r) rewrite R | R2 = refl
      aux (Dμ-dwn x dx ∷ ps) (e ∷ es) | .x  , chE | [ R ] 
          | yes refl | [ R2 ] with gapply dx (red x)
      aux (Dμ-dwn x dx ∷ ps) (e ∷ es) | .x  , chE | [ R ] 
          | yes refl | [ R2 ] | nothing = refl
      aux (Dμ-dwn x dx ∷ ps) (e ∷ es) | .x  , chE | [ R ] 
          | yes refl | [ R2 ] | just (red r) 
        rewrite R | R2 = cong (λ P → gapplyL P (chE ++ es) >>= gIns r >>= safeHead) 
                          (≡-Dμ-lift {d1 = ps} {d2 = p1 (normalize* ps)} (aux ps))
      
\end{code}
