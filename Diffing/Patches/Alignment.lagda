\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff
open import Diffing.Patches.Diff.Functor
open import Diffing.Patches.Residual
open import Relation.Binary.PropositionalEquality

module Diffing.Patches.Alignment where
\end{code}

  Our definition of alignment is slightly different from
  the one found in Marco's thesis.

  He defines two patches to be aligned if they 
  have the same source. In our terms, this means that for every object x,
  patches d1 and d2 are aligned iff (gapply d1 x succeeds iff gapply d2 succeeds)

  We use the partiality of residuals to define alignment.

%<*Aligned>
\begin{code}
  Aligned : {n : ℕ}{t : Tel n}{ty : U n}
          → (d1 d2 : Patch t ty)
          → Set
  Aligned d1 d2 = Is-Just (d1 / d2)
\end{code}
%</Aligned>

  Since residuals are symmetric, alignment is also symmetric.

%<*aligned-sym>
\begin{code}
  aligned-sym : {n : ℕ}{t : Tel n}{ty : U n}
              → {d1 d2 : Patch t ty}
              → Aligned d1 d2
              → Aligned d2 d1
  aligned-sym {d1 = d1} {d2} j 
    with residual-symmetry-thm d1 d2 (p2 (Is-Just-≡ j))
  ...| op , hip = ≡-Is-Just hip
\end{code}
%<\aligned-sym>

  But then, sometimes we want to pattern match on aligned patches only,
  so here we provide a relation over patches.

  (TODO)
    Do I really need this... I mean, having this datatype
    would grealty simplify residuals, and provide a ground for
    speaking about diverging patches.

begin{code}
  mutual
    data A : {n : ℕ}{t : Tel n}{ty : U n} 
           → Patch t ty → Patch t ty → Set
        where
      -- A-id-l : {n : ℕ}{t : Tel n}{a : U n}{d : Patch t a} → A D-id d
      -- A-id-r : {n : ℕ}{t : Tel n}{a : U n}{d : Patch t a} → A d D-id

      A-unit : {n : ℕ}{t : Tel n} → A {n} {t} D-unit D-unit

      A-inl  : {n : ℕ}{t : Tel n}{a b : U n}{p1 p2 : Patch t a}
             → A p1 p2 → A {ty = a ⊕ b} (D-inl p1) (D-inl p2)

      A-isl  : {n : ℕ}{t : Tel n}{a b : U n}{p1 : Patch t a}
               {xa : ElU a t}{xb : ElU b t}

              → Is-Just (gapply p1 xa) → A (D-inl p1) (D-setl xa xb)
      A-sil  : {n : ℕ}{t : Tel n}{a b : U n}{p1 : Patch t a}
               {xa : ElU a t}{xb : ElU b t}
              → Is-Just (gapply p1 xa) → A (D-setl xa xb) (D-inl p1)

      A-sl   : {n : ℕ}{t : Tel n}{a b : U n}
               {xa : ElU a t}{xb xb' : ElU b t}
             → A (D-setl xa xb) (D-setl xa xb')

      A-inr  : {n : ℕ}{t : Tel n}{a b : U n}{p1 p2 : Patch t b}
             → A p1 p2 → A {ty = a ⊕ b} (D-inr p1) (D-inr p2)

      A-isr  : {n : ℕ}{t : Tel n}{a b : U n}{p1 : Patch t b}
               {xb : ElU b t}{xa : ElU a t}
             → Is-Just (gapply p1 xb) → A (D-inr p1) (D-setr xb xa)

      A-sir  : {n : ℕ}{t : Tel n}{a b : U n}{p1 : Patch t b}
               {xb : ElU b t}{xa : ElU a t}
             → Is-Just (gapply p1 xb) → A (D-setr xb xa) (D-inr p1) 

      A-sr   : {n : ℕ}{t : Tel n}{a b : U n}
               {xa : ElU b t}{xb xb' : ElU a t}
             → A (D-setr xa xb) (D-setr xa xb')

      A-pair : {n : ℕ}{t : Tel n}{a b : U n}
               {p1 p2 : Patch t a}{q1 q2 : Patch t b}
             → A p1 p2 → A q1 q2 → A (D-pair p1 q1) (D-pair p2 q2)
      
      A-β    : {n : ℕ}{t : Tel n}{a : U (suc n)}{b : U n}
               {d1 d2 : Patch (tcons b t) a}
             → A d1 d2 → A (D-β d1) (D-β d2)
  
      A-top  : {n : ℕ}{t : Tel n}{a : U n}
               {d1 d2 : Patch t a}
             → A d1 d2 → A (D-top d1) (D-top d2)

      A-pop  : {n : ℕ}{t : Tel n}{a b : U n}
               {d1 d2 : Patch t b}
             → A d1 d2 → A {t = tcons a t} (D-pop d1) (D-pop d2) 

      A-mu   : {n : ℕ}{t : Tel n}{a : U (suc n)}
               {d1 d2 : Patchμ t a}
             → Aμ d1 d2 → A (D-mu d1) (D-mu d2) 

    data Aμ : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
            → Patchμ t ty → Patchμ t ty → Set
        where
      Aμ-nil  : {n : ℕ}{t : Tel n}{ty : U (suc n)}
              → Aμ {n} {t} {ty} [] []

      Aμ-insl : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                {x : ValU ty t}
              → Aμ d1 d2 → Aμ (Dμ-ins x ∷ d1) d2

      Aμ-insr : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                {x : ValU ty t}
              → Aμ d1 d2 → Aμ d1 (Dμ-ins x ∷ d2)

      Aμ-inin : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                {x y : ValU ty t}
              → Aμ d1 d2 → Aμ (Dμ-ins x ∷ d1) (Dμ-ins y ∷ d2)

      Aμ-dlcp : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                {x : ValU ty t}
              → Aμ d1 d2 → Aμ (Dμ-del x ∷ d1) (Dμ-cpy x ∷ d2)

      Aμ-cpdl : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                {x : ValU ty t}
              → Aμ d1 d2 → Aμ (Dμ-cpy x ∷ d1) (Dμ-del x ∷ d2)

      Aμ-dldl : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                {x : ValU ty t}
              → Aμ d1 d2 → Aμ (Dμ-del x ∷ d1) (Dμ-del x ∷ d2)

      Aμ-dwcp : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                {x : ValU ty t}{dx : Patch t (β ty u1)}
              → Aμ d1 d2 → Aμ (Dμ-dwn x dx ∷ d1) (Dμ-cpy x ∷ d2)

      Aμ-cpdw : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                {x : ValU ty t}{dx : Patch t (β ty u1)}
              → Aμ d1 d2 → Aμ (Dμ-cpy x ∷ d1) (Dμ-dwn x dx ∷ d2)

      Aμ-dwdl : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                {x : ValU ty t}{dx : Patch t (β ty u1)}
              → Aμ d1 d2 → Aμ (Dμ-dwn x dx ∷ d1) (Dμ-del x ∷ d2)

      Aμ-dldw : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                {x : ValU ty t}{dx : Patch t (β ty u1)}
              → Aμ d1 d2 → Aμ (Dμ-del x ∷ d1) (Dμ-dwn x dx ∷ d2)

      Aμ-dwdw : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : Patchμ t ty}
                {x : ValU ty t}{dx dy : Patch t (β ty u1)}
              → A dx dy → Aμ d1 d2 → Aμ (Dμ-dwn x dx ∷ d1) (Dμ-dwn x dy ∷ d2)
end{code}


  Which then allows us to prove that our notion of alignment
  implies the one Marco uses. To prove the reverse implication
  just use aligned-sym

begin{code}
  open import Diffing.Utils.Monads
  open Monad {{...}}

  >>=-Is-Just : ∀{a}{A B : Set a}{x : Maybe A}
                {f : A → Maybe B}
              → Is-Just (x >>= f)
              → Is-Just x
  >>=-Is-Just {x = nothing} ()
  >>=-Is-Just {x = just x} _ = indeed x
end{code}

%<*aligned-correct>
begin{code}
  mutual
    aligned-correct : {n : ℕ}{t : Tel n}{ty : U n}
                → (d1 d2 : Patch t ty)
                → (x : ElU ty t)
                → Is-Just (gapply d1 x)
                → Is-Just (gapply d2 x)
                → A d1 d2
    aligned-correct (D-A ()) _ _ _ _ 
    aligned-correct _ (D-A ()) _ _ _
    -- aligned-correct D-id d2 x p1 p2 = A-id-l
    -- aligned-correct d1 D-id x p1 p2 = A-id-r
    aligned-correct D-unit D-unit x p1 p2 = A-unit
    aligned-correct (D-inl d1) (D-inl d2) (inl x) p1 p2 
      = A-inl (aligned-correct d1 d2 x (<M>-Is-Just p1) (<M>-Is-Just p2))
    aligned-correct (D-inl d1) (D-setl x y) (inl k) p1 p2
      with x ≟-U k 
    aligned-correct (D-inl d1) (D-setl x y) (inl k) p1 () | no ¬p
    ...| yes p rewrite p = A-isl (<M>-Is-Just p1)
    
    aligned-correct (D-inl d1) (D-setr x y) (inl k) p1 ()
    aligned-correct (D-inl d1) (D-inr d2) (inl x) p1 ()
    aligned-correct (D-inl d1) d2 (inr x) () p2
    aligned-correct (D-inr d1) d2 (inl x) () p2
    aligned-correct (D-inr d1) (D-inl d2) (inr x) p1 ()
    aligned-correct (D-setl x y) d2 (inr k) () p2
    aligned-correct (D-inr d1) (D-setl x y) (inr k) p1 ()
    aligned-correct (D-setl x y) (D-setr w z) (inl k) p1 ()
    aligned-correct (D-setl x y) (D-inr d2) (inl k) p1 ()
    aligned-correct (D-setr x y) d2 (inl k) () p2
    aligned-correct (D-setr x y) (D-setl x₁ x₂) (inr k) p1 ()
    aligned-correct (D-setr x y) (D-inl d2) (inr k) p1 ()

    aligned-correct (D-inr d1) (D-inr d2) (inr x) p1 p2 
      = A-inr (aligned-correct d1 d2 x (<M>-Is-Just p1) (<M>-Is-Just p2))
    aligned-correct (D-inr d1) (D-setr x y) (inr k) p1 p2
      with x ≟-U k 
    aligned-correct (D-inr d1) (D-setr x y) (inr k) p1 () | no ¬p
    ...| yes p rewrite p = A-isr (<M>-Is-Just p1)

    aligned-correct (D-setl x y) (D-inl d2) (inl k) p1 p2 
      with x ≟-U k
    aligned-correct (D-setl x y) (D-inl d2) (inl k) () p2 | no ¬p
    ...| yes p rewrite p = A-sil (<M>-Is-Just p2)
    aligned-correct (D-setl x y) (D-setl w z) (inl k) p1 p2
      with x ≟-U k 
    aligned-correct (D-setl x y) (D-setl w z) (inl k) () p2 | no ¬p
    ...| yes x≡k with w ≟-U k
    aligned-correct (D-setl x y) (D-setl w z) (inl k) p1 () | yes x≡k | no ¬p
    ...| yes w≡k rewrite trans x≡k (sym w≡k) = A-sl
    
    
    
    aligned-correct (D-setr x y) (D-inr d2) (inr k) p1 p2
      with x ≟-U k
    aligned-correct (D-setr x y) (D-inr d2) (inr k) () p2 | no ¬p
    ...| yes x≡k rewrite x≡k = A-sir (<M>-Is-Just p2)
    
    aligned-correct (D-setr x y) (D-setr w z) (inr k) p1 p2
      with x ≟-U k 
    aligned-correct (D-setr x y) (D-setr w z) (inr k) () p2 | no ¬p
    ...| yes x≡k with w ≟-U k
    aligned-correct (D-setr x y) (D-setr w z) (inr k) p1 () | yes x≡k | no ¬p
    ...| yes w≡k rewrite trans x≡k (sym w≡k) = A-sr

    aligned-correct (D-pair d1 d2) (D-pair d3 d4) (x1 , x2) p1 p2 
      with gapply d1 x1 | inspect (gapply d1) x1
    aligned-correct (D-pair d1 d2) (D-pair d3 d4) (x1 , x2) () p2 | nothing | _
    ...| just m | [ R1 ] with gapply d3 x1 | inspect (gapply d3) x1
    aligned-correct (D-pair d1 d2) (D-pair d3 d4) (x1 , x2) p1 () 
       | just m | [ R1 ] | nothing | r
    ...| just n | [ R2 ] 
       = A-pair (aligned-correct d1 d3 x1 (≡-Is-Just R1) (≡-Is-Just R2)) 
                (aligned-correct d2 d4 x2 (<M>-Is-Just p1) (<M>-Is-Just p2))
    
    aligned-correct (D-β d1) (D-β d2) (red x) p1 p2 
      = A-β (aligned-correct d1 d2 x (<M>-Is-Just p1) (<M>-Is-Just p2))
    aligned-correct (D-top d1) (D-top d2) (top x) p1 p2 
      = A-top (aligned-correct d1 d2 x (<M>-Is-Just p1) (<M>-Is-Just p2))
    aligned-correct (D-pop d1) (D-pop d2) (pop x) p1 p2 
      = A-pop (aligned-correct d1 d2 x (<M>-Is-Just p1) (<M>-Is-Just p2))
    aligned-correct (D-mu d1) (D-mu d2) x p1 p2 
      = A-mu (alignedμ-correct d1 d2 (x ∷ []) (>>=-Is-Just p1) (>>=-Is-Just p2))

    alignedμ-correct : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                → (d1 d2 : Patchμ t ty)
                → (x : List (ElU (μ ty) t))
                → Is-Just (gapplyL d1 x)
                → Is-Just (gapplyL d2 x)
                → Aμ d1 d2
    alignedμ-correct _  (Dμ-A () ∷ d2) _ p1 p2
    alignedμ-correct (Dμ-A () ∷ d2) _ _ p1 p2

    alignedμ-correct [] [] x p1 p2 = Aμ-nil
    
    alignedμ-correct [] (Dμ-ins x ∷ d2) [] p1 p2 
      = Aμ-insr (alignedμ-correct [] d2 [] p1 (>>=-Is-Just p2))
    alignedμ-correct (Dμ-ins x ∷ d1) [] [] p1 p2 
      = Aμ-insl (alignedμ-correct d1 [] [] (>>=-Is-Just p1) p2)

    alignedμ-correct [] (Dμ-del x ∷ d2) [] p1 ()
    alignedμ-correct [] (Dμ-cpy x ∷ d2) [] p1 ()
    alignedμ-correct [] (Dμ-dwn x x₁ ∷ d2) [] p1 ()
    alignedμ-correct [] (x ∷ d2) (x₁ ∷ x₂) () p2
    alignedμ-correct (Dμ-del x ∷ d1) [] [] () p2
    alignedμ-correct (Dμ-cpy x ∷ d1) [] [] () p2
    alignedμ-correct (Dμ-dwn x x₁ ∷ d1) [] [] () p2
    alignedμ-correct (x ∷ d1) [] (x₁ ∷ x₂) p1 ()
    alignedμ-correct (Dμ-ins x ∷ d1) (Dμ-del x₁ ∷ d2) [] p1 ()
    alignedμ-correct (Dμ-ins x ∷ d1) (Dμ-cpy x₁ ∷ d2) [] p1 ()
    alignedμ-correct (Dμ-ins x ∷ d1) (Dμ-dwn x₁ x₂ ∷ d2) [] p1 ()
    alignedμ-correct (Dμ-del x ∷ d1) (x₁ ∷ d2) [] () p2
    alignedμ-correct (Dμ-cpy x ∷ d1) (x₁ ∷ d2) [] () p2
    alignedμ-correct (Dμ-dwn x x₁ ∷ d1) (x₂ ∷ d2) [] () p2

    alignedμ-correct (Dμ-ins x ∷ d1) (Dμ-ins x₁ ∷ d2) [] p1 p2 
      = Aμ-inin (alignedμ-correct {!!} {!!} {!!} {!!} {!!})
    
    alignedμ-correct (x ∷ d1) (x₁ ∷ d2) (x₂ ∷ x₃) p1 p2 = {!!}
end{code}
%</aligned-correct>
