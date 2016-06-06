\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Patches.D

module Diffing.Patches.Properties.WellFounded where
\end{code}

%<*WF-def>
\begin{code}
  WF : {A : TU→Set}{n : ℕ}{t : T n}{ty : U n}
     → D A t ty → Set
  WF {A} {n} {t} {ty} p
    = Σ (ElU ty t × ElU ty t)
        (λ xy → D-src p ≡ just (p1 xy) × D-dst p ≡ just (p2 xy))
\end{code}
%</WF-def>


%<*D-inl-wf-type>
\begin{code}
  D-inl-wf : {A : TU→Set}{n : ℕ}{t : T n}{ty tv : U n}
           → (p : D A t ty)
           → WF (D-inl {b = tv} p)
           → WF p
\end{code}
%</D-inl-wf-type>
%<*D-inl-wf-def>
\begin{code}
  D-inl-wf p ((x , y) , (hx , hy))
    = {!!}
\end{code}
%</D-inl-wf-def>
 
