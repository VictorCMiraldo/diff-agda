\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Map
open import Diffing.Utils.Propositions

open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties.Simple using (+-comm)
open import Data.List using (drop)

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

Closing it, though, requires some care in how we define it.

\begin{code}
  safeHd : {A : Set} → List A → Maybe (A × List A)
  safeHd [] = nothing
  safeHd (x ∷ xs) = just (x , xs)
\end{code}

%<*plug-type>
\begin{code}
  plug : {n : ℕ}{t : Tel n}{a : U n}{b : U (suc n)}
       → ElU b (tcons u1 t) 
       → List (ElU a t)
       → Maybe (ElU b (tcons a t) × List (ElU a t))
\end{code}
%</plug-type
\begin{code}
  plug el l = gmapSt (MCons (λ _ → safeHd) mapSt-id) el l
\end{code}

%<*mu-close>
\begin{code}
  μ-close : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
          → Openμ t ty → Maybe (ElU (μ ty) t × List (ElU (μ ty) t))
  μ-close (hd , ch) 
    = mu ∘₁ plug hd ch
\end{code}
%</mu-close>

Now, let us start proving a few lemmas over μ-close.

%<*plug-just-lemma-type>
\begin{code}
  plug-just-lemma 
    : {n : ℕ}{t : Tel n}{b : U (suc n)}{a : U n}
    → (el : ElU b (tcons u1 t))
    → (l : List (ElU a t))
    → arity-lvl fz el ≤ length l
    → Σ (ElU b (tcons a t))
        (λ ba → plug el l ≡ just (ba , drop (arity-lvl fz el) l))
\end{code}
%</plug-just-lemma-type>
\begin{code}
  plug-just-lemma el l prf = trustme
    where
      postulate trustme : {A : Set} → A
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
  μ-close-resp-arity prf = trustme
    where
      postulate trustme : {A : Set} → A
\end{code}
