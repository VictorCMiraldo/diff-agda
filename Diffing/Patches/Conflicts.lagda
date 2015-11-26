\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Patches.Diff
open import Diffing.Patches.Diff.Functor using (forget; forgetμ)

module Diffing.Patches.Conflicts where
\end{code}

  Before jumping into the definition of merge, it is important to
  have a clear notion of which are the possible conflicts we can
  face.

  There are two kinds of conflicts:
    * Update conflicts, which involve one patch
      updating a value that is either deleted
      or updated differently in another patch

    * Grow conflicts, which involve how a fixed-point
      value grow.

  Grow conflicts are easier to solve automatically.
  Depending on the fix-point we can arrange grows in
  different forms and translate them to inserts,
  whereas Update conflicts will require human intervention,
  as we can't know which update to prefer.

  An interesting point for future research, though,
  is to make rules, depentent on ty, on how to solve
  different conflicts. Certain file-format semantics
  might give important clues as to which update to prefer.

%<*C-def>
\begin{code}
  data C : {n : ℕ} → Tel n → U n → Set where
    UpdUpd : {n : ℕ}{t : Tel n}{a b : U n}
           → ElU (a ⊕ b) t → ElU (a ⊕ b) t → ElU (a ⊕ b) t → C t (a ⊕ b)
    DelUpd : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → ValU a t → ValU a t → C t (μ a)
    UpdDel : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → ValU a t → ValU a t → C t (μ a)
    GrowL  : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → ValU a t → C t (μ a)
    GrowLR : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → ValU a t → ValU a t → C t (μ a)
    GrowR  : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → ValU a t → C t (μ a)
\end{code}
%</C-def>

\begin{code}
  C₀ : Set
  C₀ = Σ ℕ (λ n → Σ (Tel n × U n) (λ k → C (p1 k) (p2 k)))

  on-C₀ : ∀{a}{A : {m : ℕ} → Tel m → U m → Set a}
        → ({n : ℕ}{t : Tel n}{ty : U n} → C t ty → A t ty) 
        → C₀ → Σ ℕ (λ n → Σ (Tel n × U n) (λ k → A (p1 k) (p2 k)))
  on-C₀ f (n , (t , ty) , x) = n , (t , ty) , f x

  on-C₀-Set : ({n : ℕ}{t : Tel n}{ty : U n} → C t ty → Set) 
            → C₀ → Set
  on-C₀-Set f (n , (t , ty) , x) = f x
\end{code}

%<*IsGrow>
\begin{code}
  IsGrow : {n : ℕ}{t : Tel n}{ty : U n} → C t ty → Set
  IsGrow (GrowL _)    = Unit
  IsGrow (GrowR _)    = Unit
  IsGrow (GrowLR _ _) = Unit
  IsGrow _ = ⊥
\end{code}
%</IsGrow>

%<*IsUpd>
\begin{code}
  IsUpd : {n : ℕ}{t : Tel n}{ty : U n} → C t ty → Set
  IsUpd (UpdUpd _ _ _) = Unit
  IsUpd (UpdDel _ _)   = Unit
  IsUpd (DelUpd _ _)   = Unit
  IsUpd _ = ⊥
\end{code}
%</IsUpd>

  An important observation is that conflicts are symmetric:

%<*C-sym>
\begin{code}
  C-sym : {n : ℕ}{t : Tel n}{ty : U n} → C t ty → C t ty
  C-sym (UpdUpd o x y) = UpdUpd o y x
  C-sym (DelUpd x y) = UpdDel y x
  C-sym (UpdDel x y) = DelUpd y x
  C-sym (GrowL x)    = GrowR x
  C-sym (GrowR x)    = GrowL x
  C-sym (GrowLR x y) = GrowLR y x
\end{code}
%</C-sym>

  And we can prove this! :)
  (well, using function extensionality...)

%<*C-sym-lemma-type>
\begin{code}
  C-sym-id-lemma : {n : ℕ}{t : Tel n}{ty : U n} 
                 → C-sym ∘ C-sym ≡ id {A = C t ty}
\end{code}
%</C-sym-lemma-type>
\begin{code}
  C-sym-id-lemma = fun-ext ext
    where
      ext : {n : ℕ}{t : Tel n}{ty : U n}
          → (c : C t ty) → C-sym (C-sym c) ≡ c
      ext (UpdUpd o x y) = refl
      ext (DelUpd x y) = refl
      ext (UpdDel x y) = refl
      ext (GrowL x)    = refl
      ext (GrowLR x y) = refl
      ext (GrowR x)    = refl
\end{code}

  Some easy wrappers over residuals

%<*conflicts>
\begin{code}
  conflicts : {n : ℕ}{t : Tel n}{ty : U n}
            → Maybe (D C t ty) → List C₀
  conflicts nothing  = []
  conflicts (just p) = forget p
\end{code}
%</conflicts>

%<*conflictsμ>
\begin{code}
  conflictsμ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            → Maybe (List (Dμ C t ty)) → List C₀
  conflictsμ nothing  = []
  conflictsμ (just p) = forgetμ p
\end{code}
%</conflictsμ>
