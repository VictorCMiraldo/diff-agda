\begin{code}
open import Prelude
open import Diffing.Universe
open import Diffing.Patches.Diff.D
open import Diffing.Patches.Apply
open import Diffing.Utils.Vector using (Vec)

module Diffing.Patches.Diff.Equality where
\end{code}

  Here we will define equality on patch space.

%<*patch-eq-def>
\begin{code}
  _==ₚ_ : {n : ℕ}{t : T n}{ty : U n}(p q : D ⊥ₚ t ty) → Set
  _==ₚ_ {n} {t} {ty} p q = (x : ElU ty t) → gapply p x ≡ gapply q x
\end{code}
%</patch-eq-def>

%<*patchmu-eq-def>
\begin{code}
  _==*ₚ_ : {n i j : ℕ}{t : T n}{ty : U (suc n)}(p q : Dμ ⊥ₚ t ty i j) → Set
  _==*ₚ_ {n} {i} {j} {t} {ty} p q 
    = (x : Vec (ElU (μ ty) t) i) → gapplyL p x ≡ gapplyL q x
\end{code}
%</patchmu-eq-def>

%<*patchmu-eq-def>
\begin{code}
  _~=*ₚ_ : {n i j k l : ℕ}{t : T n}{ty : U (suc n)}
         → Dμ ⊥ₚ t ty i j → Dμ ⊥ₚ t ty k l → Set
  _~=*ₚ_ {n} {i} {j} {k} {l} {t} {ty} p q 
    = (h1 : i ≡ k)(h2 : l ≡ j)(x : Vec (ElU (μ ty) t) i) 
    → gapplyL p x ≡ subst (λ P → Maybe (Vec _ P)) h2 (gapplyL q (subst (Vec _) h1 x))
\end{code}
%</patchmu-eq-def>
