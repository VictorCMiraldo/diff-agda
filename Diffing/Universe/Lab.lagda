\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Ops
open import Diffing.Universe.MuUtils
open import Diffing.Universe.Equality
open import Diffing.Universe.Measures
open import Data.Vec as V

module Diffing.Universe.Lab where  
\end{code}

%<*transform-type>
\begin{code}
  transform : {n : ℕ}{t : Tel n}{ty : U n}
            → (f : {n : ℕ}{t : Tel n}{ty : U n} → ElU ty t → ElU ty t)
            → ElU ty t → ElU ty t
  transform {t = tnil} f el      
    = f el
  transform {t = tcons x t} f el 
    = let hdE , chE = unplug el
       in f (plug hdE (V.map (transform f) chE))
\end{code}
%</transform-type>

