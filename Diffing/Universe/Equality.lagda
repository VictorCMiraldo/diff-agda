\begin{code}
open import Prelude
open import Diffing.Universe.Syntax

module Diffing.Universe.Equality where
\end{code}

%<*eqaulity-type>
\begin{code}
  _≟-U_ : {n : ℕ}{t : Tel n}{u : U n}(x y : ElU u t) → Dec (x ≡ y)
\end{code}
%</eqaulity-type>
%<*equality-def>
\begin{code}
  _≟-U_ {u = u1} void void = yes refl

  _≟-U_ {u = a ⊕ b} (inl a1) (inl a2) with a1 ≟-U a2
  ...| yes p = yes (cong inl p)
  ...| no  p = no (p ∘ inj-inl)
  _≟-U_ {u = a ⊕ b} (inr b1) (inr b2) with b1 ≟-U b2
  ...| yes p = yes (cong inr p)
  ...| no  p = no (p ∘ inj-inr)
  _≟-U_ {u = a ⊕ b} (inl a1) (inr b2) = no (λ ())
  _≟-U_ {u = a ⊕ b} (inr b1) (inl a2) = no (λ ())

  _≟-U_ {u = a ⊗ b} (xa , ya) (xb , yb) with xa ≟-U xb
  ...| no  px = no (px ∘ p1 ∘ inj-,)
  ...| yes px with ya ≟-U yb
  ...| no  py = no (py ∘ p2 ∘ inj-,)
  ...| yes py = yes (cong₂ _,_ px py)

  _≟-U_ {u = μ u} (mu x) (mu y) with x ≟-U y
  ...| yes p = yes (cong mu p)
  ...| no  p = no (p ∘ inj-mu)
  _≟-U_ {u = vl} (top x) (top y) with x ≟-U y
  ...| yes p = yes (cong top p)
  ...| no  p = no (p ∘ inj-top)
  _≟-U_ {u = wk u} (pop x) (pop y) with x ≟-U y
  ...| yes p = yes (cong pop p)
  ...| no  p = no (p ∘ inj-pop)
  _≟-U_ {u = β F a} (red x) (red y) with x ≟-U y
  ...| yes p = yes (cong red p)
  ...| no  p = no (p ∘ inj-red)
\end{code}
%</equality-def>