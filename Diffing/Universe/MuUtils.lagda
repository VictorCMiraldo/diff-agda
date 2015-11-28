\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Map
open import Diffing.Utils.Propositions

open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties.Simple using (+-comm)
open import Data.List using (drop)
open import Relation.Binary.PropositionalEquality

module Diffing.Universe.MuUtils where
\end{code}

This module defines some generic utility functions
targeted at operations over fixed points, yet
their more general counterparts is also exported. 


(children-lvl i) takes an element and returns a list of 
terms corresponding to variables indexed by i.
%<*children-lvl>
\begin{code}
  children-lvl : {n : ℕ}{t : Tel n}{a : U n} 
               → (i : Fin n) → ElU a t 
               → List (ElU (tel-lkup i t) t)
  children-lvl i void          = []
  children-lvl i (inl el)      = children-lvl i el
  children-lvl i (inr el)      = children-lvl i el
  children-lvl i (ela , elb)   = children-lvl i ela ++ children-lvl i elb
  children-lvl fz (top el)     = pop el ∷ []
  children-lvl (fs i) (top el) = []
  children-lvl fz (pop _)      = []
  children-lvl (fs i) (pop el) = map pop (children-lvl i el)
  children-lvl i (mu el)       = map unpop (children-lvl (fs i) el)
  children-lvl i (red el)      = map unpop (children-lvl (fs i) el)
\end{code}
%</children-lvl>

It's fixed point variant being the variables at lvl 0
of the opened functor.
%<*children>
\begin{code}
  children : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → ElU (μ a) t → List (ElU (μ a) t)
  children (mu el) = map unpop (children-lvl fz el)
\end{code}
%</children>

The value of a fixpoint ignores the recursive children.
%<*value>
\begin{code}
  value : {n : ℕ}{f : U (suc n)}{t : Tel n}
        → ElU (μ f) t → ElU f (tcons u1 t)
  value (mu el) = gmap (MCons (λ _ → void) map-id) el
\end{code}
%</value>

Arity counts the number of variables indexed by i.
%<*arity-lvl>
\begin{code}
  arity-lvl : {n : ℕ}{t : Tel n}{a : U n}
            → Fin n → ElU a t → ℕ
  arity-lvl i void = 0
  arity-lvl i (inl el) = arity-lvl i el
  arity-lvl i (inr el) = arity-lvl i el
  arity-lvl i (ela , elb) = arity-lvl i ela + arity-lvl i elb
  arity-lvl fz (top el) = 1
  arity-lvl (fs i) (top el) = 0
  arity-lvl fz (pop el) = 0
  arity-lvl (fs i) (pop el) = arity-lvl i el
  arity-lvl i (mu el) = arity-lvl (fs i) el
  arity-lvl i (red el) = arity-lvl (fs i) el  
\end{code}
%</arity-lvl>

And it's fixed point variant counts the number
of variables indexed by zero in the opened functor.
%<*arity>
\begin{code}
  arity : {n : ℕ}{t : Tel n}{a : U (suc n)}
        → ElU (μ a) t → ℕ
  arity (mu el) = arity-lvl fz el
\end{code}
%</arity>

A few lemmas might come in handy

\begin{code}
  open import Data.List.Properties
    using (length-map; length-++)
\end{code}

%<*children-arity-lemma-type>
\begin{code}
  children-arity-lemma
    : {n : ℕ}{t : Tel n}{a : U (suc n)}
    → (x : ElU (μ a) t)
    → length (children x) ≡ arity x
\end{code}
%</children-arity-lemma-type>
\begin{code}
  children-arity-lemma (mu el)
    rewrite (length-map unpop (children-lvl fz el))
         = aux fz el
    where
      aux : {n : ℕ}{t : Tel n}{a : U n}
          → (i : Fin n)(x : ElU a t)
          → length (children-lvl i x) ≡ arity-lvl i x
      aux i void = refl
      aux i (inl x) = aux i x
      aux i (inr x) = aux i x
      aux i (xa , xb) = trans (length-++ (children-lvl i xa)) 
                              (cong₂ _+_ (aux i xa) (aux i xb))
      aux fz (top x)     = refl
      aux (fs i) (top x) = refl
      aux fz (pop x)     = refl
      aux (fs i) (pop x) 
        = trans (length-map pop (children-lvl i x)) 
                (aux i x)
      aux i (mu x) 
        = trans (length-map unpop (children-lvl (fs i) x)) 
                (aux (fs i) x)
      aux i (red x) 
        = trans (length-map unpop (children-lvl (fs i) x)) 
                (aux (fs i) x)
\end{code}

Now we define utilities for opening and closing fixed points.
This can be seen as a dependent-type variant of algebras,
in the categorical sense.

%<*Openmu-def>
\begin{code}
  Openμ : {n : ℕ} → Tel n → U (suc n) → Set
  Openμ t ty = ElU ty (tcons u1 t) × List (ElU (μ ty) t)
\end{code}
%</Openmu-def>

Opening a fixed point is pretty simple, we already have the 
generic functions that do so.

%<*mu-open>
\begin{code}
  μ-open : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
         → ElU (μ ty) t → Openμ t ty
  μ-open (mu el) = value (mu el) , children (mu el)
\end{code}
%</mu-open>

\begin{code}
  μ-open-arity-lemma : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
                       {a : ElU (μ ty) t}{hdA : ElU ty (tcons u1 t)}
                       {chA : List (ElU (μ ty) t)}
                     → μ-open a ≡ (hdA , chA)
                     → arity-lvl fz hdA ≡ length chA
  μ-open-arity-lemma {a = mu a} refl = trustme
    where
      postulate trustme : ∀{a}{A : Set a} → A
\end{code}

Closing it, though, requires some care in how we define it.

\begin{code}
  safeHd : {A : Set} → List A → Maybe (A × List A)
  safeHd [] = nothing
  safeHd (x ∷ xs) = just (x , xs)
\end{code}

%<*plug-type>
\begin{code}
  plug : {n m : ℕ}{a : U m}{t : Tel (suc n)}{b : U (suc n)}
       → (m≤n : LEQ (suc m) (suc n))
       → ElU b t
       → List (ElU a (tel-drop (LEQ-dec m≤n) t))
       → Maybe (ElU b (tel-subst m≤n a t) × List (ElU a (tel-drop (LEQ-dec m≤n) t)))
\end{code}
%</plug-type>
\begin{code}
  plug m≤n el l = gmapSt (mapF m≤n) el l
    where
      mapF : {n m : ℕ}{a : U m}{t : Tel n}
          → (m≤n : LEQ (suc m) n)
          → MapSt (List (ElU a (tel-drop (LEQ-dec m≤n) t)))
                  t (tel-subst m≤n a t)
      mapF {m = m} {t = tcons t ts} LEQ-refl 
        = MCons (λ _ → safeHd) mapSt-id
      mapF {m = m} {t = tcons t ts} (LEQ-step prf) 
        = MExt (mapF prf)
\end{code}

%<*mu-close>
\begin{code}
  μ-close : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
          → Openμ t ty → Maybe (ElU (μ ty) t × List (ElU (μ ty) t))
  μ-close (hd , ch) 
    = mu ∘₁ plug LEQ-refl hd ch
\end{code}
%</mu-close>

Now, let us start proving a few lemmas over μ-close.

%<*plug-just-lemma-type>
\begin{code}
  plug-just-lemma 
    : {n m : ℕ}{a : U m}{t : Tel (suc n)}{b : U (suc n)}
    → (m≤n : LEQ (suc m) (suc n))
    → (el : ElU b t)
    → (l : List (ElU a (tel-drop (LEQ-dec m≤n) t)))
    → arity-lvl (Δ-Fin (LEQ-unstep m≤n)) el ≤ length l
    → Σ (ElU b (tel-subst m≤n a t))
        (λ ba → plug m≤n el l ≡ just (ba , drop (arity-lvl (Δ-Fin (LEQ-unstep m≤n)) el) l))
\end{code}
%</plug-just-lemma-type>
\begin{code}
  plug-just-lemma prf void l ar 
    = void , refl
  plug-just-lemma prf (inl el) l ar
    with plug-just-lemma prf el l ar
  ...| el' , res = inl el' , ∘₁-intro inl res
  plug-just-lemma prf (inr el) l ar = {!!}
  plug-just-lemma prf (el , el₁) l ar = {!!}
  plug-just-lemma LEQ-refl (top el) [] ()
  plug-just-lemma (LEQ-step prf) (top el) [] ar 
    = {!!}
  plug-just-lemma prf (top el) (x ∷ l) ar 
    = {!!}
  plug-just-lemma prf (pop el) l ar = {!!}
  plug-just-lemma prf (mu el) l ar 
    with plug-just-lemma (LEQ-step prf) el l {!!}
  ...| el' , res = mu el' , ∘₁-intro mu {!res!}
  plug-just-lemma prf (red el) l ar = {!!}
\end{code}

Now we need some lemmas stating that μ-open and
μ-close witness an "isomorpihms". The correct way
of defining them would be using vectors indexed by the
terms arity. But that's too much of a hassle, and
for applying patches it's nice if closing a μ term
returns the unused part of the children list.

%<*mu-close-resp-arity-lemma>
\begin{code}
  μ-close-resp-arity
    : {n : ℕ}{t : Tel n}{ty : U (suc n)}{a : ElU (μ ty) t}
      {hdA : ElU ty (tcons u1 t)}{chA l : List (ElU (μ ty) t)}
    → μ-open a ≡ (hdA , chA)
    → μ-close (hdA , chA ++ l) ≡ just (a , l)
\end{code}
%</mu-close-resp-arity-lemma>
\begin{code}
  μ-close-resp-arity {a = a} {hdA} {chA} {l} prf 
  {-
    with μ-open-arity-lemma prf
  ...| pa
    with plug-just-lemma hdA (chA ++ l) 
           (subst (λ L → L ≤ length (chA ++ l)) (sym pa) (length-≤ chA))
  ...| (res , prf2)
    = begin
      (mu ∘₁ gmapSt (MCons (λ _ → safeHd) mapSt-id) hdA (chA ++ l))
    ≡⟨ cong (_∘₁_ mu) prf2 ⟩
     (mu ∘₁ just (res , drop (arity-lvl fz hdA) (chA ++ l)))
    ≡⟨ cong (λ x → mu ∘₁ just (res , drop x (chA ++ l))) pa ⟩
      (mu ∘₁ just (res , drop (length chA) (chA ++ l)))
    ≡⟨ cong (λ x → mu ∘₁ just (res , x)) (drop-++-id {l = chA}) ⟩
      (mu ∘₁ just (res , l))
    ≡⟨ refl ⟩
      just (mu res , l)
    ≡⟨ cong (λ x → just (x , l)) trustme ⟩
     just (a , l)
    ∎
    -} = trustme
    where
      open ≡-Reasoning
      postulate trustme : {A : Set} → A
\end{code}

%<*mu-close-fails>
\begin{code}
  μ-close-fail
    : {n : ℕ}{t : Tel n}{ty : U (suc n)}
      (x : ElU ty (tcons u1 t))(l : List (ElU (μ ty) t))
    → suc (length l) ≤ arity-lvl fz x 
    → μ-close (x , l) ≡ nothing
\end{code}
%</mu-close-fails>
\begin{code}
  μ-close-fail prf = trustme
    where
      postulate trustme : {A : Set} → A
\end{code}
