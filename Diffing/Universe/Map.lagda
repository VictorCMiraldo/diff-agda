\begin{code}
open import Prelude
open import Level renaming (zero to lz; suc to ls)
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

  A monadic variant of map, so we can have more functionality.

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

%<*gmapM-id>
\begin{code}
  open Lawfull {{...}}

  gmapM-id : {M : Set → Set}{{ m : Monad M }}{{ laws : Lawfull M }}
           → {n : ℕ}{t : Tel n}{ty : U n}
           → (el : ElU ty t)
           → gmapM {M} {{m}} mapM-id el ≡ return el
  gmapM-id void = refl
  gmapM-id {M} {{m}} (inl el) 
    rewrite gmapM-id {M} {{m}} el
      = left-id
  gmapM-id {M} {{m}} (inr el) 
    rewrite gmapM-id {M} {{m}} el
      = left-id
  gmapM-id {M} {{m}} {{laws}} (ela , elb) 
    rewrite gmapM-id {M} {{m}} ela
          | gmapM-id {M} {{m}} elb
      = trans left-id left-id
  gmapM-id {M} {{m}} (top el) 
    rewrite gmapM-id {M} {{m}} el
      = left-id
  gmapM-id {M} {{m}} (pop el) 
    rewrite gmapM-id {M} {{m}} el
      = left-id
  gmapM-id {M} {{m}} (mu el) 
    rewrite gmapM-id {M} {{m}} el
      = left-id
  gmapM-id {M} {{m}} (red el) 
    rewrite gmapM-id {M} {{m}} el
      = left-id
\end{code}
%</gmapM-id>
