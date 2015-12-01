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

%<*mapM-compose>
\begin{code}
  mapM-∘ : {M : Set → Set}{{m : Monad M}}
         → {n : ℕ}{as bs cs : Tel n}
         → MapM M as bs → MapM M bs cs → MapM M as cs
  mapM-∘ Empty Empty = Empty
  mapM-∘ (MCons x ma) (MCons y mb) = MCons (λ a → x a >>= y) (mapM-∘ ma mb)
  mapM-∘ (MCons x ma) (MExt mb)    = MCons (λ a → x a >>= gmapM mb) (mapM-∘ ma mb) 
  mapM-∘ (MExt ma) (MCons x mb)    = MCons (λ a → gmapM ma a >>= x) (mapM-∘ ma mb)
  mapM-∘ (MExt ma) (MExt mb)       = MExt (mapM-∘ ma mb)
\end{code}
%</mapM-compose>

%<*gmapM-∘>
begin{code}
  open Lawfull {{...}}

  gmapM-∘ : {M : Set → Set}{{ m : Monad M }}{{ laws : Lawfull M }}
          → {n : ℕ}{as bs cs : Tel n}{ty : U n}
          → (ab : MapM M as bs)(bc : MapM M bs cs)
          → (el : ElU ty as)
          → (gmapM ab el >>= gmapM bc) ≡ gmapM (mapM-∘ ab bc) el
  gmapM-∘ ab Empty void = {!!}
  gmapM-∘ ab (MCons x bc) void = {!!}
  gmapM-∘ ab (MExt bc) void = {!!}
  gmapM-∘ ab bc (inl el) = {!!}
  gmapM-∘ ab bc (inr el) = {!!}
  gmapM-∘ ab bc (el , el₁) = {!!}
  gmapM-∘ ab bc (top el) = {!!}
  gmapM-∘ ab bc (pop el) = {!!}
  gmapM-∘ ab bc (mu el) = {!!}
  gmapM-∘ ab bc (red el) = {!!}
end{code}
%</gmapM-id>


We can define a "comsuming morphism" for the carrier of a monoid
in a somewhat orderly fashion:

begin{code}
  open import Algebra
  open Monoid {{...}}

  data Fold : {n : ℕ} → Tel n → Set → Set1 where
    Empty : {A : Set} → Fold tnil A
    FCons : {A : Set}{n : ℕ}{t : Tel n}{a : U n}
          → (A → A)
          → (ElU a t → A → A)
          → Fold t A
          → Fold (tcons a t) A

  fold-ext : {A : Set}{n : ℕ}{t : Tel n}{a : U n} → Fold t A → Fold (tcons a t) A
  fold-ext f = FCons id (const id) f

  fold-trivial : {A : Set}{n : ℕ}{t : Tel n} → Fold t A
  fold-trivial {t = tnil}      = Empty
  fold-trivial {t = tcons x t} = fold-ext fold-trivial

  gfold : {n : ℕ}{t : Tel n}{a : U n}
        → (m : Monoid lz lz) → Fold t (Monoid.Carrier m) 
        → ElU a t → (Monoid.Carrier m)
  gfold m f void = Monoid.ε m
  gfold m f (inl el) = gfold m f el
  gfold m f (inr el) = gfold m f el
  gfold m f (el , el') = Monoid._∙_ m (gfold m f el) (gfold m f el')
  gfold m (FCons p t f) (top el) = t el (gfold m f el)
  gfold m (FCons p t f) (pop el) = p (gfold m f el)
  gfold m f (mu el) = gfold m (fold-ext f) el
  gfold m f (red el) = gfold m (fold-ext f) el

  open import Data.Nat.Properties.Simple

  arity : {n : ℕ}{t : Tel n}{a : U n}{b : U (suc n)}
        → ElU b (tcons a t) → ℕ
  arity el = gfold {!!} {!!} {!!}
    where
      m : Monoid _ _
      m = record 
          { Carrier = ℕ 
          ; _≈_ = _≡_ 
          ; _∙_ = _+_ 
          ; ε = 0 
          ; isMonoid = record { isSemigroup = {!!} ; identity = (λ x → {!refl!}) , {!!} } }

  children : {n : ℕ}{t : Tel n}{a : U n}{b : U (suc n)}
           → ElU b (tcons a t) → List (ElU a t)
  children el = {!!}

  open import Diffing.Utils.Propositions using (++-length)

  el : ElU (μ (vl ⊕ ((wk vl ⊗ wk vl) ⊕ wk vl))) (tcons u1 tnil)
  el = mu (inl (top (mu (inr (inr (pop (top void)))))))

  a2 : ElU (vl ⊗ vl) (tcons u1 tnil)
  a2 = top void , top void 
end{code}
