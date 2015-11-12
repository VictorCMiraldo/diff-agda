\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff

module Diffing.Patches.Diff.Properties where
\end{code}

%<*DiscreteEq>
\begin{code}
  _⇔_ : Set → Set → Set
  x ⇔ y = (x → y) × (y → x)
\end{code}
%</DiscreteEq>

%<*Aligned>
\begin{code}
  Aligned : {n : ℕ}{t : Tel n}{ty : U n}
          → (d1 d2 : D t ty) → Set
  Aligned {n} {t} {ty} d1 d2 
    = (x : ElU ty t) → (gapply d1 x ≡ nothing) ⇔ (gapply d2 x ≡ nothing)
\end{code}
%</Aligned>

%<*AlignedL>
\begin{code}
  AlignedL : {n : ℕ}{t : Tel n}{ty : U (suc n)}
           → (d1 d2 : List (Dμ t ty)) → Set
  AlignedL {n} {t} {ty} d1 d2 
    = (x : List (ElU (μ ty) t)) → (gapplyL d1 x ≡ nothing) ⇔ (gapplyL d2 x ≡ nothing)
\end{code}
%</AlignedL>

%<*AlignedL-elim-lemmas>
\begin{code}
  alignedL-nil-nil : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                  → AlignedL {t = t} {ty = ty} [] []
  alignedL-nil-nil x = (λ z → z) , (λ z → z)

  alignedL-del-elim : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                → {el : ValU ty t}
                → {d1 d2 : List (Dμ t ty)}
                → AlignedL d1 d2 → AlignedL d1 (Dμ-del el ∷ d2) → ⊥
  alignedL-del-elim {d1 = []} a1 a2 with p2 (a2 []) refl
  ...| ()
  alignedL-del-elim {d1 = Dμ-ins x ∷ d1} a1 a2 with p2 (a2 []) refl
  ...| r = {!!}
  alignedL-del-elim {d1 = Dμ-del x ∷ d1} a1 a2 = {!a2 !}
  alignedL-del-elim {d1 = Dμ-cpy x ∷ d1} a1 a2 = {!!}
  alignedL-del-elim {d1 = Dμ-dwn x ∷ d1} a1 a2 = {!a2 !}
