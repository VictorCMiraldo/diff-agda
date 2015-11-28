\begin{code}
open import Prelude
open import Level renaming (zero to lz)
open import Diffing.Universe.Syntax

module Diffing.Universe.Map where

  open import Diffing.Utils.Monads
  open Monad {{...}}
\end{code}

This definition is entirely from McBride.

%<*Map-def>
\begin{code}
  data Map : {n : ℕ} → Tel n → Tel n → Set where
    Empty : Map tnil tnil
    MCons : {n : ℕ}{a b : U n}{as bs : Tel n} 
          → (ElU a as → ElU b bs) → Map as bs → Map (tcons a as) (tcons b bs)
    MExt  : {n : ℕ}{a : U n}{as bs : Tel n}
          → Map as bs → Map (tcons a as) (tcons a bs)
\end{code}
%</Map-def>

%<*map-id>
\begin{code}
  map-id : {n : ℕ}{t : Tel n} → Map t t
  map-id {t = tnil}      = Empty
  map-id {t = tcons x t} = MExt map-id
\end{code}
%</map-id>

%<*gmap>
\begin{code}
  gmap : {n : ℕ}{t : U n}{as bs : Tel n} 
       → Map as bs → ElU t as → ElU t bs
  gmap m void       = void
  gmap m (inl el)   = inl (gmap m el)
  gmap m (inr el)   = inr (gmap m el)
  gmap m (el , elb) = gmap m el , gmap m elb
  gmap (MCons x m) (top el) = top (x el)
  gmap (MExt m) (top el)    = top (gmap m el)
  gmap (MCons x m) (pop el) = pop (gmap m el)
  gmap (MExt m) (pop el)    = pop (gmap m el)
  gmap m (mu el)    = mu (gmap (MExt m) el)
  gmap m (red x)    = red (gmap (MExt m) x)
\end{code}
%</gmap>

Sometimes we want to have access to a bit more information
while traversing a term.

%<*MapSt-def>
\begin{code}
  data MapSt (S : Set) : {n : ℕ} → Tel n → Tel n → Set where
    Empty : MapSt S tnil tnil
    MCons : {n : ℕ}{a b : U n}{as bs : Tel n}
          → (ElU a as → S → Maybe ((ElU b bs) × S)) → MapSt S as bs
          → MapSt S (tcons a as) (tcons b bs)
    MExt  : {n : ℕ}{a : U n}{as bs : Tel n}
          → MapSt S as bs → MapSt S (tcons a as) (tcons a bs)
\end{code}
%</MapSt-def>

%<*mapSt-id>
\begin{code}
  mapSt-id : {S : Set}{n : ℕ}{t : Tel n} → MapSt S t t
  mapSt-id {t = tnil}      = Empty
  mapSt-id {t = tcons x t} = MExt mapSt-id
\end{code}
%</mapSt-id>

\begin{code}
  _∘₁_ : {A B C : Set} → (A → C) → Maybe (A × B) → Maybe (C × B)
  _ ∘₁ nothing      = nothing
  f ∘₁ just (x , y) = just (f x , y)

  ∘₁-intro : {A B C : Set}(f : A → C){x : Maybe (A × B)}{y : A}{z : B}
           → x ≡ just (y , z) → (f ∘₁ x) ≡ just (f y , z)
  ∘₁-intro f refl = refl
\end{code}

%<*gmapSt>
\begin{code}
  gmapSt : {S : Set}{n : ℕ}{t : U n}{as bs : Tel n} 
         → MapSt S as bs → ElU t as → S → Maybe (ElU t bs × S)
  gmapSt m void s               = just (void , s)
  gmapSt m (inl el) s           = inl ∘₁ gmapSt m el s
  gmapSt m (inr el) s           = inr ∘₁ gmapSt m el s
  gmapSt (MCons f m) (top el) s = top ∘₁ f el s
  gmapSt (MExt m) (top el) s    = top ∘₁ gmapSt m el s 
  gmapSt (MCons x m) (pop el) s = pop ∘₁ gmapSt m el s
  gmapSt (MExt m) (pop el) s    = pop ∘₁ gmapSt m el s
  gmapSt m (mu el) s            = mu ∘₁ gmapSt (MExt m) el s
  gmapSt m (red el) s           = red ∘₁ gmapSt (MExt m) el s
  gmapSt m (ela , elb) s 
    with gmapSt m ela s
  ...| nothing          = nothing
  ...| just (ela' , s1) = (_,_ ela') ∘₁ gmapSt m elb s1
\end{code}
%</gmapSt>

%<*MapSt-def>
\begin{code}
  data MapStSet (S : Set) : {n : ℕ} → Tel n → Set1 where
    Empty : MapStSet S tnil
    MCons : {n : ℕ}{a : U n}{as : Tel n}
          → (ElU a as → S → Set) → MapStSet S as
          → MapStSet S (tcons a as)
    MExt  : {n : ℕ}{a : U n}{as : Tel n}
          → MapStSet S as → MapStSet S (tcons a as)
\end{code}
%</MapSt-def>

%<*gmapStInd>
\begin{code}

\end{code}
%</gmapStInd>


For the situations a simple accumulator doesn't
work, we give a monadic extension of gmap.

%<*MapM-def>
\begin{code}
  data MapM (M : Set → Set){{ isM : Monad M }} 
       : {n : ℕ} → Tel n → Tel n → Set 
   where
    Empty : MapM M tnil tnil
    MCons : {n : ℕ}{a b : U n}{as bs : Tel n}
          → (ElU a as → M (ElU b bs)) → MapM M as bs 
          → MapM M (tcons a as) (tcons b bs)
    MExt  : {n : ℕ}{a : U n}{as bs : Tel n}
          → MapM M as bs → MapM M (tcons a as) (tcons a bs)
\end{code}
%</MapM-def>

%<*mapM-id>
\begin{code}
  mapM-id : {M : Set → Set}{{ m : Monad M }}{n : ℕ}{t : Tel n} → MapM M t t
  mapM-id {t = tnil}      = Empty
  mapM-id {t = tcons x t} = MExt mapM-id
\end{code}
%</mapM-id>

%<*gmapM>
\begin{code}
  gmapM : {M : Set → Set}{{ isM : Monad M }}{n : ℕ}{t : U n}{as bs : Tel n} 
        → MapM M as bs → ElU t as → M (ElU t bs)
  gmapM m void = return void
  gmapM m (inl el) = (gmapM m el) >>= (return ∘ inl)
  gmapM m (inr el) = (gmapM m el) >>= (return ∘ inr)
  gmapM m (el , elb) 
    = gmapM m el
    >>= \el' → gmapM m elb
    >>= return ∘ (_,_ el')
  gmapM (MCons x m) (top el) = (x el) >>= (return ∘ top)
  gmapM (MExt m)    (top el) = (gmapM m el) >>= (return ∘ top)
  gmapM (MCons x m) (pop el) = gmapM m el >>= return ∘ pop
  gmapM (MExt m) (pop el) = gmapM m el >>= return ∘ pop
  gmapM m (mu el) = gmapM (MExt m) el >>= return ∘ mu
  gmapM m (red el) = gmapM (MExt m) el >>= return ∘ red
\end{code}
%</gmapM>
