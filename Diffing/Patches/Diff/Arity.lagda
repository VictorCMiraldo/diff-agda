\begin{code}
open import Prelude
open import Data.Nat.Properties.Simple
  using (+-comm; +-assoc)
open import Relation.Binary.PropositionalEquality
open import Diffing.Universe
open import Diffing.Universe.Operations.Properties
open import Diffing.Universe.Plugging.Properties
open import Diffing.Patches.Diff
open import Diffing.Utils.Vector

module Diffing.Patches.Diff.Arity where

  open D-Substs
\end{code}

  This module proves that we could have defined Dμ-dwn as:

    Dμ-dwn : {i j : ℕ}(dx : D A (u1 ∷ t) ty)
           → Dμ A t ty (#i 0 dx + i) (#o 0 dx + j)
           → Dμ A t ty (suc i) (suc j)

  Given that counting the arities of a patch or counting
  the arities of it's source and destination is the same thing.

  We begin by introducing the arity counting functions:

%<*dmu-arity-type>
\begin{code}
  #i* #o* : ∀{a}{n i j : ℕ}{t : T n}{ty : U (suc n)}
            {A : {n : ℕ} → T n → U n → Set a}
          → ℕ → Dμ A t ty i j → ℕ
\end{code}
%</dmu-arity-type>
%<*d-arity-type>
\begin{code}
  #i #o : ∀{a}{n : ℕ}{t : T n}{ty : U n}{A : {n : ℕ} → T n → U n → Set a}
        → ℕ → D A t ty → ℕ
\end{code}
%</d-arity-type>
\begin{code}
  #i i (D-A x) = 0
  #i i D-unit = 0
  #i i (D-inl d) = #i i d
  #i i (D-inr d) = #i i d
  #i i (D-setl x _) = ar i x
  #i i (D-setr x _) = ar i x
  #i i (D-pair da db) = #i i da + #i i db
  #i i (D-mu x) = #i* i x
  #i i (D-def d) = #i (suc i) d
  #i zero (D-top d) = 1
  #i (suc i) (D-top d) = #i i d
  #i zero (D-pop d) = 0
  #i (suc i) (D-pop d) = #i i d

  #o i (D-A x) = 0
  #o i D-unit = 0
  #o i (D-inl d) = #o i d
  #o i (D-inr d) = #o i d
  #o i (D-setl _ x) = ar i x
  #o i (D-setr _ x) = ar i x
  #o i (D-pair da db) = #o i da + #o i db
  #o i (D-mu x) = #o* i x
  #o i (D-def d) = #o (suc i) d
  #o zero (D-top d) = 1
  #o (suc i) (D-top d) = #o i d
  #o zero (D-pop d) = 0
  #o (suc i) (D-pop d) = #o i d

  #i* i (Dμ-A x d) = #i* i d
  #i* i (Dμ-del x d) = ar (suc i) x + #i* i d
  #i* i (Dμ-ins x d) = #i* i d
  #i* i (Dμ-dwn x y d) = ar (suc i) x + #i* i d
  #i* i Dμ-end = 0

  #o* i (Dμ-A x d) = 0
  #o* i (Dμ-del x d) = #o* i d
  #o* i (Dμ-ins x d) = ar (suc i) x + #o* i d
  #o* i (Dμ-dwn x y d) = ar (suc i) y + #o* i d
  #o* i Dμ-end = 0
\end{code}

  Some subject reduction lemmas

\begin{code}
  #i*-substo-lemma 
    : {n i j k : ℕ}{t : T n}{ty : U (suc n)}
    → (p : k ≡ i)(d : Dμ ⊥ₚ t ty j k)(v : ℕ)
    → #i* v (μ-subst-o p d) ≡ #i* v d
  #i*-substo-lemma refl d v = refl

  #i*-substi-lemma
    : {n i j k : ℕ}{t : T n}{ty : U (suc n)}
    → (p : k ≡ i)(d : Dμ ⊥ₚ t ty k j)(v : ℕ)
    → #i* v (μ-subst-i p d) ≡ #i* v d
  #i*-substi-lemma refl d v = refl

  #i*-substio-lemma 
    : {n i j k l : ℕ}{t : T n}{ty : U (suc n)}
    → (p : k ≡ i)(q : j ≡ l)(d : Dμ ⊥ₚ t ty k j)(v : ℕ)
    → #i* v (μ-subst-io p q d) ≡ #i* v d
  #i*-substio-lemma refl refl d v = refl

  #o*-substo-lemma 
    : {n i j k : ℕ}{t : T n}{ty : U (suc n)}
    → (p : k ≡ i)(d : Dμ ⊥ₚ t ty j k)(v : ℕ)
    → #o* v (μ-subst-o p d) ≡ #o* v d
  #o*-substo-lemma refl d v = refl

  #o*-substi-lemma
    : {n i j k : ℕ}{t : T n}{ty : U (suc n)}
    → (p : k ≡ i)(d : Dμ ⊥ₚ t ty k j)(v : ℕ)
    → #o* v (μ-subst-i p d) ≡ #o* v d
  #o*-substi-lemma refl d v = refl

  #o*-substio-lemma 
    : {n i j k l : ℕ}{t : T n}{ty : U (suc n)}
    → (p : k ≡ i)(q : j ≡ l)(d : Dμ ⊥ₚ t ty k j)(v : ℕ)
    → #o* v (μ-subst-io p q d) ≡ #o* v d
  #o*-substio-lemma refl refl d v = refl
\end{code}

\begin{code}
  {-# TERMINATING #-}
\end{code}
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

\begin{code}
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

  private
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
      → ar (suc i) (μ-hd x)
      + #i* i (μ-subst-io (μ-lal x) (μ-lal y) (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys)))
      ≡ ar i x + ar* i xs
    gdiffL-#i-aux-dwn i x y xs ys
      rewrite #i*-substio-lemma (μ-lal x) (μ-lal y) (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys)) i
            = trans (cong (λ P → ar (suc i) (μ-hd x) + P) 
                          (trans (gdiffL-#i*-lemma (μ-ch x ++ xs) (μ-ch y ++ ys) i) 
                                 (ar*-++-commute i (μ-ch x) xs))) 
             (trans (sym (+-assoc (ar (suc i) (μ-hd x)) (ar* i (μ-ch x)) (ar* i xs))) 
                    (cong (λ P → P + ar* i xs) (sym (μ-arity-lemma x i))))

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
      → ar (suc i) (μ-hd y)
      + #o* i (μ-subst-io (μ-lal x) (μ-lal y) (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys)))
      ≡ ar i y + ar* i ys
    gdiffL-#o-aux-dwn i x y xs ys
      rewrite #o*-substio-lemma (μ-lal x) (μ-lal y) (gdiffL (μ-ch x ++ xs) (μ-ch y ++ ys)) i
            = trans (cong (λ P → ar (suc i) (μ-hd y) + P) 
                          (trans (gdiffL-#o*-lemma (μ-ch x ++ xs) (μ-ch y ++ ys) i) 
                                 (ar*-++-commute i (μ-ch y) ys))) 
             (trans (sym (+-assoc (ar (suc i) (μ-hd y)) (ar* i (μ-ch y)) (ar* i ys))) 
                    (cong (λ P → P + ar* i ys) (sym (μ-arity-lemma y i))))
\end{code}

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

%<*gapply-arity-type>
\begin{code}
  gapply-arity : {n : ℕ}{t : T n}{ty : U n}(i : ℕ)
               → (d : Patch t ty)(x x' : ElU ty t)
               → gapply d x ≡ just x'
               → (#i i d ≡ ar i x) × (#o i d ≡ ar i x')
\end{code}
%</gapply-arity-type>


  Proving gapply-arity, however, is a whole other business. 
  Unfortunately, the proof is very complicated and cluttered
  for the gapplyL-arity lemma (which is used for recursive types).

\begin{code}
  private
    aux : {n : ℕ}{t : T n}{ty : U (suc n)}(i : ℕ)
        → (a : ValU ty t)(za : Vec (ElU (μ ty) t) (ar 0 a))
        → ar* i (toList za) ≡ ar* (suc i) (ch 0 (plugv 0 a (vmap pop za)))
    aux {n} {t} {ty} i a za 
      rewrite ch-plugv-lemma 0 a (vmap pop za)
            | toList-vmap (pop {a = μ ty}) za
            = sym (ar*-pop i (toList za))

    inl-inr-⊥ : {n : ℕ}{t : T n}{a b : U n}{xa : ElU a t}{xb : ElU b t}
              → inl xa ≡ inr xb → ⊥
    inl-inr-⊥ ()
\end{code}


%<*gapplyL-arity-type>
\begin{code}
  gapplyL-arity : {n k j : ℕ}{t : T n}{ty : U (suc n)}(i : ℕ)
                → (d : Dμ ⊥ₚ t ty k j)(x : Vec (ElU (μ ty) t) k)(x' : Vec (ElU (μ ty) t) j)
                → gapplyL d x ≡ just x'
                → (#i* i d ≡ ar*v i x) × (#o* i d ≡ ar*v i x')
\end{code}
%</gapplyL-arity-type>

%<*gapply-arity-def>
\begin{code}
  gapply-arity i (D-A ()) x y prf 
  gapply-arity i D-unit unit unit prf = refl , refl
  gapply-arity i (D-inl d) (inl x) (inl y) prf 
    with <M>-elim prf
  ...| .y , refl , prf2 = gapply-arity i d x y prf2
  gapply-arity i (D-inr d) (inr x) (inr y) prf
    with <M>-elim prf
  ...| .y , refl , prf2 = gapply-arity i d x y prf2
  gapply-arity i (D-setl a b) (inl x) (inr y) prf
    with a ≟-U x
  ...| no _  = ⊥-elim (Maybe-⊥ (sym prf))
  ...| yes p = cong (ar i) p , cong (ar i) (inj-inr (just-inj prf))
  gapply-arity i (D-setr a b) (inr x) (inl y) prf
    with a ≟-U x
  ...| no _  = ⊥-elim (Maybe-⊥ (sym prf))
  ...| yes p = cong (ar i) p , cong (ar i) (inj-inl (just-inj prf))

  gapply-arity i (D-inl d) (inl x) (inr y) prf 
    = ⊥-elim (inl-inr-⊥ (sym (p1 (p2 (<M>-elim prf)))))
  gapply-arity i (D-inl d) (inr x) (inl y) ()
  gapply-arity i (D-inl d) (inr x) (inr y) ()
  gapply-arity i (D-inr d) (inl x) (inl y) ()
  gapply-arity i (D-inr d) (inl x) (inr y) ()
  gapply-arity i (D-inr d) (inr x) (inl y) prf 
    = ⊥-elim (inl-inr-⊥ (p1 (p2 (<M>-elim prf))))
  
  gapply-arity i (D-setl a b) (inl x) (inl y)
    with a ≟-U x
  ...| no _  = λ ()
  ...| yes _ = λ ()
  gapply-arity i (D-setr a b) (inr x) (inr y)
    with a ≟-U x
  ...| no _  = λ ()
  ...| yes _ = λ ()
  gapply-arity i (D-setl a b) (inr x) (inl y)
    = λ ()
  gapply-arity i (D-setl a b) (inr x) (inr y)
    = λ ()
  gapply-arity i (D-setr a b) (inl x) (inl y)
    = λ ()
  gapply-arity i (D-setr a b) (inl x) (inr y)
    = λ ()
  
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
\end{code}
%</gapply-arity-def>

%<*gapplyL-arity-def>
\begin{code}
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
  gapplyL-arity i (Dμ-dwn ex ey d) (x ∷ xs) (y ∷ ys) prf
    with μ-hd x ≟-U ex
  ...| no  _ = ⊥-elim (Maybe-⊥ (sym prf)) 
  gapplyL-arity i (Dμ-dwn .(μ-hd x) ey d) (x ∷ xs) (y ∷ ys) prf 
     | yes refl with <M>-elim prf
  gapplyL-arity i (Dμ-dwn .(μ-hd x) ey d) (x ∷ xs) (._ ∷ ._) prf | yes refl
     | el , refl , qel with vsplit (ar 0 ey) el | inspect (vsplit (ar 0 ey)) el
  ...| v1 , v2 | [ R ]
     rewrite p1 (gapplyL-arity i d (μ-chv x ++v xs) el qel)
           | p2 (gapplyL-arity i d (μ-chv x ++v xs) el qel) 
     = μ-ar-open-lemma x xs i 
     , sym (trans (cong (λ P → P + ar*v i v2) (ar-lemma (suc i) 0 (plugv 0 ey (vmap pop v1)))) 
           (trans (cong (λ P → ar (suc i) P + ar* (suc i) (ch 0 (plugv 0 ey (vmap pop v1))) + ar*v i v2)
                     (fgt-plugv-lemma 0 ey (vmap pop v1))) 
           (trans (+-assoc (ar (suc i) ey)
                     (ar* (suc i) (ch 0 (plugv 0 ey (vmap pop v1)))) (ar*v i v2)) 
           (cong (λ P → ar (suc i) ey + P) 
                 (sym (trans (cong (ar*v i) (vsplit-lemma v1 v2 el R)) 
                      (trans (ar*v-reduce i v1 v2) 
                             (cong (λ P → P + ar*v i v2) (aux i ey v1)))))))))
\end{code}
%</gapplyL-arity-def>
