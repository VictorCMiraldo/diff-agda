\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Ops
open import Diffing.Utils.Vector
  using (toList; vec; length-toList; vmap; vec-toList)

module Diffing.Universe.MuUtils where
\end{code}

This module defines some generic utility functions
targeted at operations over fixed points. They arise
as specific instances of the operations defined in
Diffing.Universe.Ops.

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
  μ-open (mu el) with unplug el
  ...| hd , ch = hd , toList ch
\end{code}
%</mu-open>

\begin{code}
  μ-hd : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
       → ElU (μ ty) t → ElU ty (tcons u1 t)
  μ-hd = p1 ∘ μ-open

  μ-ch : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
       → ElU (μ ty) t → List (ElU (μ ty) t)
  μ-ch = p2 ∘ μ-open
\end{code}

It is trivially true that opening a fixpoint preserves it arity.

\begin{code}
  μ-open-arity-lemma 
    : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
    → (el : ElU (μ ty) t)
    → length (p2 (μ-open el)) ≡ arity (p1 (μ-open el))
  μ-open-arity-lemma {n} {t} {ty} (mu el) 
    with unplug el
  ...| hd , ch 
     = length-toList (vmap unpop (vec (children-lvl fz el) _))
\end{code}

Closing it, though, requires some care in how we define it.

\begin{code}
  open import Data.Nat
    using (_≤_; s≤s; z≤n)

  list-split : {m : ℕ}{A : Set}(l : List A)
             → m ≤ length l
             → Σ (List A × List A) (λ ls → length (p1 ls) ≡ m)
  list-split [] z≤n = ([] , []) , refl
  list-split (x ∷ l) z≤n = ([] , x ∷ l) , refl
  list-split (x ∷ l) (s≤s p) with list-split l p
  ...| (la , lb) , prf = (x ∷ la , lb) , (cong suc prf)

  list-split-lemma 
    : {m : ℕ}{A : Set}(l1 l2 : List A){p : m ≤ length (l1 ++ l2)}
    → (q : length l1 ≡ m)
    → list-split (l1 ++ l2) p ≡ ((l1 , l2) , q)
  list-split-lemma [] [] {z≤n} refl = refl
  list-split-lemma [] (x ∷ l2) {z≤n} refl = refl
  list-split-lemma (x ∷ l1) l2 {s≤s p} refl
    with list-split-lemma l1 l2 {p} refl
  ...| hip rewrite hip = refl
\end{code}

%<*mu-close>
\begin{code}
  μ-close : {n : ℕ}{t : Tel n}{ty : U (suc n)} 
          → Openμ t ty → Maybe (ElU (μ ty) t × List (ElU (μ ty) t))
  μ-close (hd , ch) with arity hd ≤?-ℕ length ch
  ...| no  _ = nothing
  ...| yes p with list-split ch p
  ...| (chA , rest) , prf 
     = just (mu (plug hd (vec chA prf)) , rest)
\end{code}
%</mu-close>

Now we need some lemmas stating that μ-open and
μ-close witness an "isomorpihms". The correct way
of defining them would be using vectors indexed by the
terms arity. But that's too much of a hassle, and
for applying patches it's nice if closing a μ term
returns the unused part of the children list.

\begin{code}
  length-lemma 
    : {n : ℕ}{A : Set}(l1 l2 : List A)
    → length l1 ≡ n → n ≤ length (l1 ++ l2)
  length-lemma [] l2 refl = z≤n
  length-lemma (x ∷ l1) l2 refl = s≤s (length-lemma l1 l2 refl)
\end{code}

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
  μ-close-resp-arity {a = mu a} {l = l} refl
    with arity-lvl fz (p1 (μ-open (mu a))) ≤?-ℕ length (p2 (μ-open (mu a)) ++ l)
  ...| no ¬q = ⊥-elim (¬q (length-lemma (p2 (μ-open (mu a))) l (μ-open-arity-lemma (mu a))))
  ...| yes q 
    rewrite list-split-lemma 
       (toList (vmap unpop (vec (children-lvl fz a) 
               (trans (ch-ar-lemma-lvl fz a) (forget-arity-lemma fz a))))) l
       {p = q}
       (length-toList (vmap unpop (vec (children-lvl fz a) 
               (trans (ch-ar-lemma-lvl fz a) (forget-arity-lemma fz a)))))
     = cong (λ P → just (mu P , l)) 
       (subst (λ P → plug-lvl fz (forget fz a) (vmap pop P) ≡ a) 
         (sym (vec-toList (vmap unpop (vec (children-lvl fz a)
              (trans (ch-ar-lemma-lvl fz a) (forget-arity-lemma fz a)))))) 
         (subst (λ P → plug-lvl fz (forget fz a) P ≡ a) 
           (sym (vmap-lemma (vec (children-lvl fz a)
                            (trans (ch-ar-lemma-lvl fz a) (forget-arity-lemma fz a))) 
                            (λ { (pop x) → refl }))) 
           (sym (plug-lvl-correct fz a))))
\end{code} 
