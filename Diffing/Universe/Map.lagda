\begin{code}
open import Prelude
open import Level renaming (zero to lz; suc to ls)
open import Data.Nat using (_≤_; s≤s; z≤n)
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
  gmap-id : {n : ℕ}{t : Tel n} → Map t t
  gmap-id {t = tnil}      = Empty
  gmap-id {t = tcons x t} = MExt gmap-id
\end{code}
%</map-id>

%<*gmap>
\begin{code}
  gmap : {n : ℕ}{t : U n}{as bs : Tel n} 
       → Map as bs → ElU t as → ElU t bs
  gmap m unit       = unit
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

