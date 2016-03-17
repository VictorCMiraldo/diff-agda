\begin{code}
open import Prelude

open import Diffing.Universe.Syntax
open import Diffing.Universe.Operations
open import Diffing.Universe.Operations.Properties
open import Diffing.Utils.Vector

module Diffing.Universe.Plugging where
\end{code}


%<*unplug-type>
\begin{code}
  unplug : {n : ℕ}{t : T n}{ty : U n}
         → (i : ℕ)(el : ElU ty t)
         → Σ (ElU ty (tel-forget i t))
             (Vec (ElU (tel-lkup i t) t) ∘ (ar i))
\end{code}
%</unplug-type>
\begin{code}
  unplug i el
    = fgt i el
    , vec (ch i el) (trans (ch-ar-lemma i el) (fgt-ar-lemma i el))
\end{code}

%<*plug-type>
\begin{code}
  plug : {n : ℕ}{t : T n}{ty : U n}
       → (i : ℕ)(el : ElU ty (tel-forget i t))
       → Vec (ElU (tel-lkup i t) t) (ar i el)
       → ElU ty t
\end{code}
%</plug-type>
\begin{code}
  plug {ty = u0} i () v
  plug {ty = u1} i el v = unit
  plug {ty = ty ⊕ tv} i (inl el) v = inl (plug i el v)
  plug {ty = ty ⊕ tv} i (inr el) v = inr (plug i el v)
  plug {ty = ty ⊗ tv} i (ela , elb) v 
    = let va , vb = vsplit (ar i ela) v
      in plug i ela va , plug i elb vb
  plug {ty = def F x} i (red el) v 
    = red (plug (suc i) el (vmap pop v))
  plug {ty = μ ty} i (mu el) v
    = mu (plug (suc i) el (vmap pop v))
  plug {t = t ∷ ts} {ty = var} zero (top el) (pop v ∷ []) 
    = top v
  plug {t = t ∷ ts} {ty = var} (suc i) (top el) v 
    = top (plug i el (vmap unpop v))
  plug {t = t ∷ ts} {ty = wk ty} zero (pop el) v 
    = pop el
  plug {t = t ∷ ts} {ty = wk ty} (suc i) (pop el) v
    = pop (plug i el (vmap unpop v))
\end{code}

