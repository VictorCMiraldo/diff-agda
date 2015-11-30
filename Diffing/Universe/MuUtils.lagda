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

And it's fixed point variant counts the number
of variables indexed by zero in the opened functor.

\begin{code}

  open import Diffing.Utils.Monads
  open Monad {{...}}

  arity : {n : ℕ}{t : Tel n}{a : U (suc n)}{b : U n}
        → ElU a (tcons b t) → ℕ
  arity el = p2 (ST.run (gmapM (MCons incState mapM-id) el) 0)
    where
      incState : {n : ℕ}{t : Tel n}{ty : U n}
               → ElU ty t → ST ℕ (ElU ty t)
      incState x = get >>= (λ s → put s >> return x)
\end{code}
%</arity>

A few lemmas might come in handy

\begin{code}
  open import Data.List.Properties
    using (length-map; length-++)
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

Instead of defining open using value and children,
let's do it the other way around, and define children.

Actually, we could do it generically, indeed:
  open : ElU ty (tcons a t) → ElU (tcons u1 t) × List (ElU a t)
This actually gives us a way to deconstruct a meta-tree (in the form of a term) into an
actual agda rose-tree. Even easier would be
to do: 
  open : ElU ty (tcons a t) → Σ (ElU ty (tcons u1 t)) (Vec (ElU a t) ∘ arity)

the closing then would only need the maybe when transforming
the input list into a vector.

%<*mu-open>
\begin{code}
  μ-open : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
         → ElU (μ ty) t → Openμ t ty
  μ-open (mu el) = ST.run (gmapM (MCons (λ x → append-st x >> return void) mapM-id) el) []
    where
      append-st : {A : Set} → A → ST (List A) Unit
      append-st a = get >>= λ l → put (a ∷ l)
\end{code}
%</mu-open>

Closing it, though, requires some care in how we define it.

\begin{code}
  safeHd : {A : Set} → List A → Maybe (A × List A)
  safeHd [] = nothing
  safeHd (x ∷ xs) = just (x , xs)
\end{code}

%<*mu-close>
\begin{code}
  μ-close : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
          → Openμ t ty → Maybe (ElU (μ ty) t × List (ElU (μ ty) t))
  μ-close (hd , ch) = close (STM.run (gmapM (MCons (λ _ → getm >>= plug) mapM-id) hd) ch)
    where
      close : {n : ℕ}{t : Tel n}{ty : U (suc n)}{B : Set}
            → Maybe (ElU ty (tcons (μ ty) t) × B) 
            → Maybe (ElU (μ ty) t × B)
      close nothing = nothing
      close (just (el , xs)) = just (mu el , xs)

      plug : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
           → List (ElU (μ ty) t) → STM (List (ElU (μ ty) t)) (ElU (μ ty) t)
      plug [] = failSTM
      plug (x ∷ xs) = putm xs >> return x    
\end{code}
%</mu-close>

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
