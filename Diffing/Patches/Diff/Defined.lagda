\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.MuUtils
open import Diffing.Universe.Equality
open import Diffing.Patches.Diff
open import Relation.Binary.PropositionalEquality

open import Data.Nat using (_≤_; z≤n; s≤s)

module Diffing.Patches.Diff.Defined where
\end{code}

  Given a definition of diff, our categorical setting
  requires that a patch is "defined" for a given object x,
  in order for it to be an arrow x → y, for some y.

  This module defines precisely what this means.

%<*Defined-def>
\begin{code}
  mutual
    data Defined : {n : ℕ}{t : Tel n}{ty : U n} 
                 → D t ty → ElU ty t → Set
                 where
      d-id   : {n : ℕ}{t : Tel n}{a : U n}{e : ElU a t} 
             → Defined D-id e
      d-void : {n : ℕ}{t : Tel n} → Defined D-void (void {t = t})
      d-inl  : {n : ℕ}{t : Tel n}{a b : U n}{e : ElU a t}{d : D t a}
             → Defined d e → Defined (D-inl {b = b} d) (inl e)
      d-setl : {n : ℕ}{t : Tel n}{a b : U n}{ea : ElU a t}{eb : ElU b t}
             → Defined (D-setl ea eb) (inl ea)
      d-inr  : {n : ℕ}{t : Tel n}{a b : U n}{e : ElU b t}{d : D t b}
             → Defined d e → Defined (D-inr {a = a} d) (inr e)
      d-setr : {n : ℕ}{t : Tel n}{a b : U n}{eb : ElU b t}{ea : ElU a t}
             → Defined (D-setr eb ea) (inr eb)
      d-pair : {n : ℕ}{t : Tel n}{a b : U n}
               {ea : ElU a t}{eb : ElU b t}
               {da : D t a}{db : D t b}
             → Defined da ea → Defined db eb 
             → Defined (D-pair da db) (ea , eb)
      d-β : {n : ℕ}{t : Tel n}{x : U n}{F : U (suc n)}
            {d : D (tcons x t) F}{el : ElU F (tcons x t)}
          → Defined d el → Defined (D-β d) (red el)
      d-top : {n : ℕ}{t : Tel n}{a : U n}{d : D t a}{el : ElU a t}
            → Defined d el → Defined {t = tcons a t} (D-top d) (top el)
      d-pop : {n : ℕ}{t : Tel n}{a b : U n}{d : D t b}{el : ElU b t}
            → Defined d el → Defined (D-pop {a = a} d) (pop el)
      d-mu  : {n : ℕ}{t : Tel n}{a : U (suc n)}{ds : List (Dμ t a)}
              {el : ElU (μ a) t}
            → Defined* ds (el ∷ []) → Defined (D-mu ds) el
      
    data Defined* : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
                  → List (Dμ t ty) → List (ElU (μ ty) t) → Set
                  where
      d*-end : {n : ℕ}{t : Tel n}{ty : U (suc n)}{x : List (ElU (μ ty) t)}
            → Defined* [] x

      d*-ins : {n : ℕ}{t : Tel n}{ty : U (suc n)}
               {es k : List (ElU (μ ty) t)}{d : List (Dμ t ty)}
               {hdE : ElU ty (tcons u1 t)}
             → Defined* d es
             → Is-Just (μ-close (hdE , k))
             → Defined* (Dμ-ins hdE ∷ d) es

      d*-del : {n : ℕ}{t : Tel n}{ty : U (suc n)}{e : ElU (μ ty) t}
               {es chE : List (ElU (μ ty) t)}{d : List (Dμ t ty)}
               {hdE : ElU ty (tcons u1 t)}
             → Defined* d (chE ++ es)
             → μ-open e ≡ (hdE , chE)
             → Defined* (Dμ-del hdE ∷ d) (e ∷ es)

      d*-cpy : {n : ℕ}{t : Tel n}{ty : U (suc n)}{e : ElU (μ ty) t}
               {es chE : List (ElU (μ ty) t)}{d : List (Dμ t ty)}
               {hdE : ElU ty (tcons u1 t)}
             → Defined* d (chE ++ es)
             → Defined* (Dμ-cpy hdE ∷ d) (e ∷ es)
\end{code}
%</Defined-def>

\begin{code}
  maybe-absurd : {A : Set}{a : A}{x : Maybe A}
               → x ≡ nothing
               → x ≡ just a
               → ⊥
  maybe-absurd refl ()

  gins→μclose : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                {x : ElU ty (tcons u1 t)}{k k' : List (ElU (μ ty) t)}
              → gIns x k ≡ just k'
              → Is-Just (μ-close (x , k))
  gins→μclose {x = x} {k} {k'} prf with μ-close (x , k)
  gins→μclose () | nothing
  ...| just rl = indeed rl

  open import Diffing.Utils.Monads
  open Monad {{...}}

  just>>= : {A B : Set}(a : Maybe A)(f : A → Maybe B){k : B} 
          → (a >>= f) ≡ just k
          → Σ (Is-Just a) (λ x → Is-Just (f (from-Just x)))
  just>>= nothing _ ()
  just>>= (just x) f {k} prf = (indeed x) , (subst Is-Just (sym prf) (indeed k))
  
\end{code}

\begin{code}
  mutual
\end{code}
%<*Defined-correct-type>
\begin{code}
    defined-correct : {n : ℕ}{t : Tel n}{ty : U n}
                    {el' : ElU ty t}(d : D t ty)(el : ElU ty t)
                  → gapply d el ≡ just el'
                  → Defined d el
\end{code}
%</Defined-correct-type>
\begin{code}
    defined-correct D-id el prf = d-id

    defined-correct D-void void prf = d-void

    defined-correct (D-inl d) (inl el) prf 
      with gapply d el | inspect (gapply d) el
    defined-correct (D-inl d) (inl el) () | nothing | _
    ...| just k | [ r ] = d-inl (defined-correct d el r)

    defined-correct (D-setr x y) (inr el) prf 
      with x ≟-U el
    defined-correct (D-setr x y) (inr el) () | no x≢el
    ...| yes x≡el rewrite x≡el = d-setr

    defined-correct (D-inr d) (inr el) prf 
      with gapply d el | inspect (gapply d) el
    defined-correct (D-inr d) (inr el) () | nothing | _
    ...| just k | [ r ] = d-inr (defined-correct d el r)

    defined-correct (D-setl x y) (inl el) prf
      with x ≟-U el
    defined-correct (D-setl x y) (inl el) () | no x≢el
    ...| yes x≡el rewrite x≡el = d-setl

    defined-correct (D-inl d) (inr el) ()
    defined-correct (D-inr d) (inl el) ()
    defined-correct (D-setl x y) (inr el) ()
    defined-correct (D-setr x y) (inl el) ()    
    
    defined-correct (D-pair da db) (ela , elb) prf 
      with gapply da ela | inspect (gapply da) ela
    defined-correct (D-pair da db) (ela , elb) () | nothing | r
    ...| just ka | [ rA ]
      with gapply db elb | inspect (gapply db) elb
    defined-correct (D-pair da db) (ela , elb) () 
       | just ka | [ rA ] | nothing | r
    ...| just kb | [ rB ] 
       = d-pair (defined-correct da ela rA) (defined-correct db elb rB)

    defined-correct (D-β d) (red el) prf
      with gapply d el | inspect (gapply d) el
    defined-correct (D-β d) (red el) () | nothing | r
    ...| just k | [ r ] = d-β (defined-correct d el r)

    defined-correct (D-top d) (top el) prf
      with gapply d el | inspect (gapply d) el
    defined-correct (D-top d) (top el) () | nothing | r
    ...| just k | [ r ] = d-top (defined-correct d el r)

    defined-correct (D-pop d) (pop el) prf
      with gapply d el | inspect (gapply d) el
    defined-correct (D-pop d) (pop el) () | nothing | r
    ...| just k | [ r ] = d-pop (defined-correct d el r)

    defined-correct (D-mu x) (mu el) prf 
      with gapplyL x (mu el ∷ []) | inspect (gapplyL x) (mu el ∷ [])
    defined-correct (D-mu x) (mu el) () | nothing | r
    ...| just k  | [ r ] = d-mu (aux x (mu el ∷ []) r)
      where
        aux : {n : ℕ}{t : Tel n}{ty : U (suc n)}
              {el' : List (ElU (μ ty) t)}(d : List (Dμ t ty))
              (el : List (ElU (μ ty) t))
              → gapplyL d el ≡ just el'
              → Defined* d el
        aux [] el prf = d*-end

        aux (Dμ-del x ∷ d) [] ()
        aux (Dμ-cpy x ∷ d) [] ()
        aux (Dμ-dwn x ∷ d) [] ()
        
        aux (Dμ-ins x ∷ d) es prf with gapplyL d es | inspect (gapplyL d) es
        aux (Dμ-ins x ∷ d) es () | nothing | _
        ...| just k  | [ R ] = d*-ins (aux d es R) (gins→μclose {x = x} {k = k} prf)            

        aux (Dμ-del x ∷ d) (e ∷ es) prf with μ-open e | inspect μ-open e
        ...| hdE , chE | [ R ] with x ≟-U hdE
        aux (Dμ-del x ∷ d) (e ∷ es) () | hdE , chE | _ | no x≢e
        ...| yes x≡e rewrite x≡e = d*-del (aux d (chE ++ es) prf) R

        aux (Dμ-cpy x ∷ d) (e ∷ es) prf with μ-open e | inspect μ-open e
        ...| hdE , chE | [ R ] with x ≟-U hdE
        aux (Dμ-cpy x ∷ d) (e ∷ es) () | hdE , chE | _ | no x≢e
        ...| yes x≡e rewrite x≡e with just>>= (gapplyL d (chE ++ es)) (gIns hdE) prf
        ...| ja , jb = d*-cpy {chE = chE} (aux d (chE ++ es) (p2 (Is-Just-≡ ja)))

        aux (Dμ-dwn x ∷ d) (e ∷ es) prf = {!!}
        
\end{code}
