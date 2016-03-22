\begin{code}
open import Prelude

open import Data.Nat.Properties.Simple
  using (+-comm; +-assoc)
open import Relation.Binary.PropositionalEquality

open import Diffing.Universe
open import Diffing.Universe.Operations.Properties
open import Diffing.Universe.Plugging.Properties

open import Diffing.Utils.Vector

module Diffing.Patches.Diff where

  open import Diffing.Patches.Diff.D public
  open import Diffing.Patches.Diff.Cost public

  open Substs
\end{code}

          Diffing
  =======================

  The type-safe variant of the diff algorithm is defined just like
  its type-UNsafe cousin.

  We do need, however, a bunch of lemmas to manipulate the indices of Dμ
  in order to make Agda happy.

  We start by declaring both gdiff and gdiffL

%<*gdiff-type>
\begin{code}
  {-# TERMINATING #-}
  gdiff : {n : ℕ}{t : T n}{ty : U n} 
        → ElU ty t → ElU ty t → Patch t ty
\end{code}
%</gdiff-type>
%<*gdiffL-type>
\begin{code}
  gdiffL : {n : ℕ}{t : T n}{ty : U (suc n)} 
         → (xs ys : List (ElU (μ ty) t)) → Dμ ⊥ₚ t ty (length xs) (length ys)
\end{code}
%</gdiffL-type>

  Lemmas relating the arity of a diff with the arity of its
  arguments follow.

%<*gdiff-ar-i-lemma-type>
\begin{code}
  gdiff-#i-lemma 
    : {n : ℕ}{t : T n}{ty : U n}
    → (x y : ElU ty t)(i : ℕ)
    → #i i (gdiff x y) ≡ ar i x
\end{code}
%</gdiff-ar-i-lemma-type>
%<*gdiff-ar-o-lemma-type>
\begin{code}
  gdiff-#o-lemma 
    : {n : ℕ}{t : T n}{ty : U n}
    → (x y : ElU ty t)(i : ℕ)
    → #o i (gdiff x y) ≡ ar i y
\end{code}
%</gdiff-ar-o-lemma-type>

  Obviously, for lists, we use ar*.

%<*gdiffL-ar-i-lemma-type>
\begin{code}
  gdiffL-#i*-lemma 
    : {n : ℕ}{t : T n}{ty : U (suc n)}
    → (xs ys : List (ElU (μ ty) t))(i : ℕ)
    → #i* i (gdiffL xs ys) ≡ ar* i xs
\end{code}
%</gdiffL-ar-i-lemma-type>
%<*gdiffL-ar-o-lemma-type>
\begin{code}
  gdiffL-#o*-lemma 
    : {n : ℕ}{t : T n}{ty : U (suc n)}
    → (xs ys : List (ElU (μ ty) t))(i : ℕ)
    → #o* i (gdiffL xs ys) ≡ ar* i ys
\end{code}
%</gdiffL-ar-o-lemma-type>

  Before the actual diffing algorithm, we still need
  to populate our back of tricks.

\begin{code}
  private
    μ-li-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
               → (x y : ElU (μ ty) t)(xs : List (ElU (μ ty) t))
               → length (μ-ch x ++ xs)
               ≡ #i 0 (gdiff (μ-hd x) (μ-hd y)) + length xs
    μ-li-lemma x y xs = trans (μ-lal x)
                          (cong (λ P → P + length xs)
                           (sym (gdiff-#i-lemma (μ-hd x) (μ-hd y) 0)))

    μ-lo-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
               → (x y : ElU (μ ty) t)(xs : List (ElU (μ ty) t))
               → length (μ-ch x ++ xs)
               ≡ #o 0 (gdiff (μ-hd y) (μ-hd x)) + length xs
    μ-lo-lemma x y xs = trans (μ-lal x)
                          (cong (λ P → P + length xs)
                           (sym (gdiff-#o-lemma (μ-hd y) (μ-hd x) 0)))

    gdiffL-#i-aux-del
      : {n : ℕ}{t : T n}{ty : U (suc n)}(i : ℕ)
      → (y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
      → #i* i (μ-subst-o (μ-lal y) (gdiffL xs (μ-ch y ++ ys))) ≡ ar* i xs
    gdiffL-#i-aux-del i y xs ys
      = trans (#i*-substo-lemma (μ-lal y) (gdiffL xs (μ-ch y ++ ys)) i) 
              (gdiffL-#i*-lemma xs (μ-ch y ++ ys) i)

    gdiffL-#i-aux-ins
      : {n : ℕ}{t : T n}{ty : U (suc n)}(i : ℕ)
      → (x : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
      → ar (suc i) (μ-hd x) + #i* i (μ-subst-i (μ-lal x) (gdiffL (μ-ch x ++ xs) ys))
      ≡ ar i x + ar* i xs
    gdiffL-#i-aux-ins i (mu x) xs ys = let mx = mu x 
      in trans (cong (λ P → ar (suc i) (μ-hd mx) + P) 
               (trans (#i*-substi-lemma (μ-lal mx) (gdiffL (μ-ch mx ++ xs) ys) i) 
               (trans (gdiffL-#i*-lemma (μ-ch mx ++ xs) ys i) 
                      (ar*-++-commute i (μ-ch mx) xs)))) 
               (trans (sym (+-assoc (ar (suc i) (μ-hd mx)) (ar* i (μ-ch mx)) (ar* i xs))) 
                      (cong (λ P → P + ar* i xs) (sym (μ-arity-lemma mx i))))

    gdiffL-#i-aux-dwn
      : {n : ℕ}{t : T n}{ty : U (suc n)}(i : ℕ)
      → (x y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
      → #i (suc i) (gdiff (μ-hd x) (μ-hd y)) 
      + #i* i (μ-subst-io (μ-li-lemma x y xs) (μ-lo-lemma y x ys) (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys)))
      ≡ ar i x + ar* i xs
    gdiffL-#i-aux-dwn i x y xs ys
      rewrite #i*-substio-lemma (μ-li-lemma x y xs) (μ-lo-lemma y x ys)  
                                (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys)) i  
            = trans (cong₂ _+_ (gdiff-#i-lemma (μ-hd x) (μ-hd y) (suc i))
                               (gdiffL-#i*-lemma (μ-ch x ++ xs) (μ-ch y ++ ys) i))
                    (trans (cong (λ P → ar (suc i) (μ-hd x) + P)
                              (ar*-++-commute i (μ-ch x) xs)) 
                    (trans
                       (sym (+-assoc (ar (suc i) (μ-hd x)) (ar* i (μ-ch x)) (ar* i xs)))
                       (cong (λ P → P + ar* i xs) (sym (μ-arity-lemma x i))))
                    )

    gdiffL-#o-aux-del
      : {n : ℕ}{t : T n}{ty : U (suc n)}(i : ℕ)
      → (y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
      → ar (suc i) (μ-hd y) + #o* i (μ-subst-o (μ-lal y) (gdiffL xs (μ-ch y ++ ys))) ≡ ar i y + ar* i ys
    gdiffL-#o-aux-del i (mu y) xs ys = let my = mu y 
      in trans (cong (λ P → ar (suc i) (μ-hd my) + P) 
               (trans (#o*-substo-lemma (μ-lal my) (gdiffL xs (μ-ch my ++ ys)) i) 
               (trans (gdiffL-#o*-lemma xs (μ-ch my ++ ys) i) 
                      (ar*-++-commute i (μ-ch my) ys)))) 
               (trans (sym (+-assoc (ar (suc i) (μ-hd my)) (ar* i (μ-ch my)) (ar* i ys))) 
                      (cong (λ P → P + ar* i ys) (sym (μ-arity-lemma my i))))
       

    gdiffL-#o-aux-ins
      : {n : ℕ}{t : T n}{ty : U (suc n)}(i : ℕ)
      → (x : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
      → #o* i (μ-subst-i (μ-lal x) (gdiffL (μ-ch x ++ xs) ys))
      ≡ ar* i ys
    gdiffL-#o-aux-ins i x xs ys
      = trans (#o*-substi-lemma (μ-lal x) (gdiffL (μ-ch x ++ xs) ys) i) 
              (gdiffL-#o*-lemma (μ-ch x ++ xs) ys i)

    gdiffL-#o-aux-dwn
      : {n : ℕ}{t : T n}{ty : U (suc n)}(i : ℕ)
      → (x y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
      → #o (suc i) (gdiff (μ-hd x) (μ-hd y)) 
      + #o* i (μ-subst-io (μ-li-lemma x y xs) (μ-lo-lemma y x ys) (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys)))
      ≡ ar i y + ar* i ys
    gdiffL-#o-aux-dwn i x y xs ys
      rewrite #o*-substio-lemma (μ-li-lemma x y xs) (μ-lo-lemma y x ys)  
                                (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys)) i  
            = trans (cong₂ _+_ (gdiff-#o-lemma (μ-hd x) (μ-hd y) (suc i))
                               (gdiffL-#o*-lemma (μ-ch x ++ xs) (μ-ch y ++ ys) i))
                    (trans (cong (λ P → ar (suc i) (μ-hd y) + P)
                              (ar*-++-commute i (μ-ch y) ys)) 
                    (trans
                       (sym (+-assoc (ar (suc i) (μ-hd y)) (ar* i (μ-ch y)) (ar* i ys)))
                       (cong (λ P → P + ar* i ys) (sym (μ-arity-lemma y i))))
                    )
\end{code}

  Now we can define auxiliar functions for computing recursive diffs
  AND taking care of their indicies.

\begin{code}
  gdiffL-ins : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (length xs) (suc (length ys))
  gdiffL-ins y xs ys = Dμ-ins (μ-hd y) (μ-subst-o (μ-lal y) (gdiffL xs (μ-ch y ++ ys)))

  gdiffL-del : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (suc (length xs)) (length ys)
  gdiffL-del x xs ys = Dμ-del (μ-hd x) (μ-subst-i (μ-lal x) (gdiffL (μ-ch x ++ xs) ys))

  gdiffL-dwn : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x y : ElU (μ ty) t)(xs ys : List (ElU (μ ty) t))
             → Dμ ⊥ₚ t ty (suc (length xs)) (suc (length ys))
  gdiffL-dwn x y xs ys 
    = Dμ-dwn (gdiff (μ-hd x) (μ-hd y)) 
             (μ-subst-io (μ-li-lemma x y xs) 
                         (μ-lo-lemma y x ys)  
                         (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys)))
\end{code}

  Finally, the actual diffing algorithm.

%<*gdiff-def>
\begin{code}
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
  gdiffL [] [] = Dμ-end
  gdiffL [] (y ∷ ys) = gdiffL-ins y [] ys
  gdiffL (x ∷ xs) [] = gdiffL-del x xs [] 
  gdiffL (x ∷ xs) (y ∷ ys) 
    =  gdiffL-ins y (x ∷ xs) ys 
    ⊓μ gdiffL-del x xs (y ∷ ys)
    ⊓μ gdiffL-dwn x y xs ys
\end{code}
%</gdiffL-def>

  Last but not least we have the proof of the arity lemmas.

\begin{code}
  gdiff-#i-lemma {ty = u0} () y i
  gdiff-#i-lemma {ty = u1} unit unit i = refl
  gdiff-#i-lemma {ty = ty ⊕ tv} (inl x) (inl y) i = gdiff-#i-lemma x y i
  gdiff-#i-lemma {ty = ty ⊕ tv} (inl x) (inr y) i = refl
  gdiff-#i-lemma {ty = ty ⊕ tv} (inr x) (inl y) i = refl
  gdiff-#i-lemma {ty = ty ⊕ tv} (inr x) (inr y) i = gdiff-#i-lemma x y i
  gdiff-#i-lemma {ty = ty ⊗ tv} (xa , xb) (ya , yb) i 
    = cong₂ _+_ (gdiff-#i-lemma xa ya i) (gdiff-#i-lemma xb yb i)
  gdiff-#i-lemma {ty = def F ty} (red x) (red y) i = gdiff-#i-lemma x y (suc i)
  gdiff-#i-lemma {ty = μ ty} (mu x) (mu y) i 
    = trans (gdiffL-#i*-lemma (mu x ∷ []) (mu y ∷ []) i) (+-comm (ar (suc i) x) zero)
  gdiff-#i-lemma {ty = var} (top x) (top y) zero = refl
  gdiff-#i-lemma {ty = var} (top x) (top y) (suc i) = gdiff-#i-lemma x y i
  gdiff-#i-lemma {ty = wk ty} (pop x) (pop y) zero = refl
  gdiff-#i-lemma {ty = wk ty} (pop x) (pop y) (suc i) = gdiff-#i-lemma x y i

  gdiff-#o-lemma {ty = u0} () y i
  gdiff-#o-lemma {ty = u1} unit unit i = refl
  gdiff-#o-lemma {ty = ty ⊕ tv} (inl x) (inl y) i = gdiff-#o-lemma x y i
  gdiff-#o-lemma {ty = ty ⊕ tv} (inl x) (inr y) i = refl
  gdiff-#o-lemma {ty = ty ⊕ tv} (inr x) (inl y) i = refl
  gdiff-#o-lemma {ty = ty ⊕ tv} (inr x) (inr y) i = gdiff-#o-lemma x y i
  gdiff-#o-lemma {ty = ty ⊗ tv} (xa , xb) (ya , yb) i 
    = cong₂ _+_ (gdiff-#o-lemma xa ya i) (gdiff-#o-lemma xb yb i)
  gdiff-#o-lemma {ty = def F ty} (red x) (red y) i = gdiff-#o-lemma x y (suc i)
  gdiff-#o-lemma {ty = μ ty} (mu x) (mu y) i 
    = trans (gdiffL-#o*-lemma (mu x ∷ []) (mu y ∷ []) i) (+-comm (ar (suc i) y) zero)
  gdiff-#o-lemma {ty = var} (top x) (top y) zero = refl
  gdiff-#o-lemma {ty = var} (top x) (top y) (suc i) = gdiff-#o-lemma x y i
  gdiff-#o-lemma {ty = wk ty} (pop x) (pop y) zero = refl
  gdiff-#o-lemma {ty = wk ty} (pop x) (pop y) (suc i) = gdiff-#o-lemma x y i

  gdiffL-#i*-lemma [] [] i = refl
  gdiffL-#i*-lemma [] (y ∷ ys) i
    = gdiffL-#i-aux-del i y [] ys
  gdiffL-#i*-lemma (x ∷ xs) [] i 
    = gdiffL-#i-aux-ins i x xs []
  gdiffL-#i*-lemma (x ∷ xs) (y ∷ ys) i 
    = ⊓μ-elim3 {P = λ d → #i* i d ≡ ar i x + ar* i xs}
        (gdiffL-ins y (x ∷ xs) ys)
        (gdiffL-del x xs (y ∷ ys))
        (gdiffL-dwn x y xs ys) 
        (gdiffL-#i-aux-del i y (x ∷ xs) ys)
        (gdiffL-#i-aux-ins i x xs (y ∷ ys))
        (gdiffL-#i-aux-dwn i x y xs ys)        

  gdiffL-#o*-lemma [] [] i = refl
  gdiffL-#o*-lemma [] (y ∷ ys) i
    = gdiffL-#o-aux-del i y [] ys
  gdiffL-#o*-lemma (x ∷ xs) [] i 
    = gdiffL-#o-aux-ins i x xs []
  gdiffL-#o*-lemma (x ∷ xs) (y ∷ ys) i 
    = ⊓μ-elim3 {P = λ d → #o* i d ≡ ar i y + ar* i ys}
        (gdiffL-ins y (x ∷ xs) ys)
        (gdiffL-del x xs (y ∷ ys))
        (gdiffL-dwn x y xs ys) 
        (gdiffL-#o-aux-del i y (x ∷ xs) ys)
        (gdiffL-#o-aux-ins i x xs (y ∷ ys))
        (gdiffL-#o-aux-dwn i x y xs ys)
\end{code}

       Application
  =========================

\begin{code}
  open import Diffing.Utils.Monads
  open Monad {{...}}

  {-# TERMINATING #-}
\end{code}
%<*gapplyL-type>
\begin{code}
  gapplyL : {n i j : ℕ}{t : T n}{ty : U (suc n)}
          → Dμ ⊥ₚ t ty i j 
          → Vec (ElU (μ ty) t) i → Maybe (Vec (ElU (μ ty) t) j)
\end{code}
%</gapplyL-type>
\end{code}
%<*gapply-type>
\begin{code}
  gapply : {n : ℕ}{t : T n}{ty : U n}
         → Patch t ty → ElU ty t → Maybe (ElU ty t)
\end{code}
%</gapply-type>
%<*gapply-def>
\begin{code}
  gapply (D-A ())

  gapply D-unit unit = just unit

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

  gapply (D-def diff) (red el) = red <M> gapply diff el
  gapply (D-top diff) (top el) = top <M> gapply diff el
  gapply (D-pop diff) (pop el) = pop <M> gapply diff el

  gapply {ty = μ ty} (D-mu d) el = head <M> gapplyL d (el ∷ [])

  private
    postulate
      hipothesis : {n : ℕ}{t : T n}{ty : U (suc n)}
                 → (d : Patch (u1 ∷ t) ty)(x x' : ValU ty t)
                 → gapply d x ≡ just x'
                 → (#i 0 d ≡ ar 0 x) × (#o 0 d ≡ ar 0 x')

  gapply-arity : {n : ℕ}{t : T n}{ty : U n}(i : ℕ)
               → (d : Patch t ty)(x x' : ElU ty t)
               → gapply d x ≡ just x'
               → (#i i d ≡ ar i x) × (#o i d ≡ ar i x')

  gIns : {n j : ℕ}{t : T n}{ty : U (suc n)}
       → (a : ValU ty t) → Vec (ElU (μ ty) t) (ar 0 a + j)
       → Vec (ElU (μ ty) t) (suc j)
  gIns a as = μ-closev a as

  gapplyL (Dμ-A () p) xs
  gapplyL Dμ-end [] = just []
  gapplyL (Dμ-del a p) (x ∷ xs) 
    with μ-hd x ≟-U a
  gapplyL (Dμ-del .(μ-hd x) p) (x ∷ xs) 
    | yes refl = gapplyL p (μ-chv x ++v xs)
  gapplyL (Dμ-del a p) (x ∷ xs) 
    | no  _ = nothing
  gapplyL (Dμ-ins a p) xs 
    = gIns a <M> gapplyL p xs
  gapplyL {i = suc i} {j = suc j} (Dμ-dwn d p) (x ∷ xs) 
    with gapply d (μ-hd x) | inspect (gapply d) (μ-hd x)
  ...| nothing | _     = nothing
  ...| just x' | [ R ] 
     = let hipi , hipo = gapply-arity 0 d (μ-hd x) x' R
        in gIns x' <M> gapplyL (μ-subst-io (cong (λ P → P + i) hipi) (cong (λ P → P + j) hipo) p) 
                               (μ-chv x ++v xs)

  {-
     with gapply-arity 0 d (μ-hd x) x' R
  ...| hipi , hipo
     rewrite hipi | hipo
           = μ-closev x' <M> gapplyL p (μ-chv x ++v xs)
  -}

  gapplyL-arity : {n k j : ℕ}{t : T n}{ty : U (suc n)}(i : ℕ)
                → (d : Dμ ⊥ₚ t ty k j)(x : Vec (ElU (μ ty) t) k)(x' : Vec (ElU (μ ty) t) j)
                → gapplyL d x ≡ just x'
                → (#i* i d ≡ ar*v i x) × (#o* i d ≡ ar*v i x')

  gapply-arity i (D-A ()) x y prf 
  gapply-arity i D-unit unit unit prf = refl , refl
  gapply-arity i (D-inl d) (inl x) (inl y) prf 
    with <M>-elim prf
  ...| .y , refl , prf2 = gapply-arity i d x y prf2
  gapply-arity i (D-inl d) (inl x) (inr y) prf = {!<M>-elim prf!}
  gapply-arity i (D-inl d) (inr x) (inl y) prf = {!!}
  gapply-arity i (D-inl d) (inr x) (inr y) prf = {!!}
  gapply-arity i (D-inr d) (inl x) (inl y) prf = {!!}
  gapply-arity i (D-inr d) (inl x) (inr y) prf = {!!}
  gapply-arity i (D-inr d) (inr x) (inl y) prf = {!!}
  gapply-arity i (D-inr d) (inr x) (inr y) prf = {!!}
  gapply-arity i (D-setl a b) (inl x) (inl y) prf = {!!}
  gapply-arity i (D-setl a b) (inl x) (inr y) prf = {!!}
  gapply-arity i (D-setl a b) (inr x) (inl y) prf = {!!}
  gapply-arity i (D-setl a b) (inr x) (inr y) prf = {!!}
  gapply-arity i (D-setr a b) (inl x) (inl y) prf = {!!}
  gapply-arity i (D-setr a b) (inl x) (inr y) prf = {!!}
  gapply-arity i (D-setr a b) (inr x) (inl y) prf = {!!}
  gapply-arity i (D-setr a b) (inr x) (inr y) prf = {!!}
  gapply-arity i (D-pair da db) (xa , xb) (ya , yb) prf 
    with gapply da xa | inspect (gapply da) xa
  ...| nothing  | _     = ⊥-elim (Maybe-⊥ (sym prf))
  ...| just xa' | [ R ] 
    with <M>-elim prf
  gapply-arity i (D-pair da db) (xa , xb) (.xa' , yb) prf 
     | just xa' | [ R ] | .yb , refl , prf2
    with gapply-arity i da xa xa' R | gapply-arity i db xb yb prf2
  ...| pa , pb | qa , qb = (cong₂ _+_ pa qa) , (cong₂ _+_ pb qb)
  gapply-arity i (D-def d) (red x) (red y) prf 
    with <M>-elim prf
  ...| .y , refl , prf2 = gapply-arity (suc i) d x y prf2
  gapply-arity zero (D-top d) (top x) (top y) prf 
    = refl , refl
  gapply-arity (suc i) (D-top d) (top x) (top y) prf 
    with <M>-elim prf
  ...| .y , refl , prf2 = gapply-arity i d x y prf2
  gapply-arity zero (D-pop d) (pop x) (pop y) prf 
    = refl , refl
  gapply-arity (suc i) (D-pop d) (pop x) (pop y) prf 
    with <M>-elim prf
  ...| .y , refl , prf2 = gapply-arity i d x y prf2
  gapply-arity i (D-mu d)  (mu x)  (mu y)  prf
    with <M>-elim prf
  ...| (.(mu y) ∷ []) , refl , prf2
     = let pi , po = gapplyL-arity i d (mu x ∷ []) (mu y ∷ []) prf2  
        in trans pi (+-comm (ar (suc i) x) zero)
         , trans po (+-comm (ar (suc i) y) zero)

  gapplyL-arity i (Dμ-A () d) xs ys prf
  gapplyL-arity i Dμ-end [] [] prf = refl , refl
  gapplyL-arity i (Dμ-del a d) (x ∷ xs) ys prf 
    with μ-hd x ≟-U a
  ...| no  _ = ⊥-elim (Maybe-⊥ (sym prf))
  gapplyL-arity i (Dμ-del .(μ-hd x) d) (x ∷ xs) ys prf | yes refl 
    = let hipi , hipo = gapplyL-arity i d (μ-chv x ++v xs) ys prf
       in trans (cong (λ P → ar (suc i) (μ-hd x) + P) (trans hipi (ar*v-reduce i (μ-chv x) xs))) 
                (trans (sym (+-assoc (ar (suc i) (μ-hd x)) (ar* i (toList (μ-chv x))) (ar*v i xs))) 
                       (cong (λ P → P + ar*v i xs) (sym (μ-arity-lemma-2 x i)))
                ) 
        , hipo
  gapplyL-arity i (Dμ-ins a d) xs (y ∷ ys) prf 
    with gapplyL d xs | inspect (gapplyL d) xs
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym prf))
  gapplyL-arity i (Dμ-ins a d) xs (._ ∷ ._) refl | just zs | [ R ]
    with vsplit (ar 0 a) zs | inspect (vsplit (ar 0 a)) zs
  ...| za , zb | [ R2 ]
     = let hipi , hipo = gapplyL-arity i d xs zs R
        in hipi , sym (
          trans (cong (λ P → P + ar*v i zb) (ar-lemma (suc i) 0 (plugv 0 a (vmap pop za))))
         (trans (cong (λ P → ar (suc i) P + ar* (suc i) (ch 0 (plugv 0 a (vmap pop za))) + ar*v i zb)
                      (fgt-plugv-lemma 0 a (vmap pop za))) 
         (trans (+-assoc (ar (suc i) a)
                   (ar* (suc i) (ch 0 (plugv 0 a (vmap pop za)))) (ar*v i zb)) 
                (cong (λ P → ar (suc i) a + P) (sym (trans hipo
                  (trans (cong (λ P → ar*v i P) (vsplit-lemma za zb zs R2)) 
                  (trans (ar*v-reduce i za zb) 
                         (cong (λ P → P + ar*v i zb) (aux i a za)) )))
                  ))
           )))
     where
       aux : {n : ℕ}{t : T n}{ty : U (suc n)}(i : ℕ)
           → (a : ValU ty t)(za : Vec (ElU (μ ty) t) (ar 0 a))
           → ar* i (toList za) ≡ ar* (suc i) (ch 0 (plugv 0 a (vmap pop za)))
       aux {n} {t} {ty} i a za 
         rewrite ch-plugv-lemma 0 a (vmap pop za)
               | toList-vmap (pop {a = μ ty}) za
               = sym (ar*-pop i (toList za))
  gapplyL-arity i (Dμ-dwn dx d) (x ∷ xs) (y ∷ ys) prf 
    with gapply dx (μ-hd x) | inspect (gapply dx) (μ-hd x)
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym prf))
  ...| just x' | [ R ] 
    = {!!} 
  {-
    with #i 0 dx | gapply-arity 0 dx (μ-hd x) x' R
  ...| .(ar 0 (μ-hd x)) | refl , hip0o = {!!}
  -}
  
  {-
    with gapply dx (μ-hd x) | inspect (gapply dx) (μ-hd x)
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym prf))
  ...| just x' | [ R ] 
    with gapply-arity 0 dx (μ-hd x) x' R
  ...| hip0i , hip0o 
     = let resi , reso = gapplyL-arity i d 
                           (subst (Vec (ElU (μ ty) t)) (cong (λ P → P + k) (sym hip0i)) (μ-chv x ++v xs)) 
                           (subst (Vec (ElU (μ ty) t)) {!!} (μ-chv y ++v ys)) 
                           {!!}
        in {!!} , {!!}
  -}
\end{code}
%</gapply-def>

%<*safeHead-def>
begin{code}
    safeHead : ∀{a}{A : Set a} → List A → Maybe A
    safeHead []       = nothing
    safeHead (x ∷ []) = just x
    safeHead _        = nothing
end{code}
%</safeHead-def>

%<*gIns-def>
begin{code}
    gIns : {n : ℕ}{t : Tel n}{ty : U (suc n)}
         → ElU ty (tcons u1 t) → List (ElU (μ ty) t) → Maybe (List (ElU (μ ty) t))
    gIns x l with μ-close (x , l)
    ...| nothing = nothing
    ...| just (r , l') = just (r ∷ l')
end{code}
%</gIns-def>

%<*gDel-def>
begin{code}
    gDel : {n : ℕ}{t : Tel n}{ty : U (suc n)}
         → ElU ty (tcons u1 t) → List (ElU (μ ty) t) → Maybe (List (ElU (μ ty) t))
    gDel x [] = nothing
    gDel {ty = ty} x (y ∷ ys) with μ-open y
    ...| hdY , chY with x ≟-U hdY
    ...| yes _ = just (chY ++ ys)
    ...| no  _ = nothing
end{code}
%</gDel-def>

%<*gapplyL-def>
begin{code}
    gapplyL : {n : ℕ}{t : Tel n}{ty : U (suc n)}
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
end{code}
%</gapplyL-def>
