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

%<*IsGrow>
\begin{code}
  IsGrow : C → Set
  IsGrow (GrowL _)    = Unit
  IsGrow (GrowR _)    = Unit
  IsGrow (GrowLR _ _) = Unit
  IsGrow _ = ⊥
\end{code}
%</IsGrow>

%<*IsUpd>
\begin{code}
  IsUpd : C → Set
  IsUpd (UpdUpd _ _ _) = Unit
  IsUpd (UpdDel _ _)   = Unit
  IsUpd (DelUpd _ _)   = Unit
  IsUpd _ = ⊥
\end{code}
%</IsUpd>

\begin{code}
  C-where : C → Σ ℕ (λ n → Tel n × U n)
  C-where (UpdUpd {n} {t} {a} {b} _ _ _) = n , (t , a ⊕ b)
  C-where (DelUpd {n} {t} {ty} _ _) = n , (t , μ ty)
  C-where (UpdDel {n} {t} {ty} _ _) = n , (t , μ ty)
  C-where (GrowL {n} {t} {ty} _)    = n , (t , μ ty)
  C-where (GrowLR {n} {t} {ty} _ _) = n , (t , μ ty)
  C-where (GrowR {n} {t} {ty} _)    = n , (t , μ ty)
\end{code}

  An important observation is that conflicts are symmetric:

%<*C-sym>
\begin{code}
  C-sym : C → C
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
  C-sym-id-lemma : C-sym ∘ C-sym ≡ id {A = C}
\end{code}
%</C-sym-lemma-type>
\begin{code}
  C-sym-id-lemma = fun-ext ext
    where
      ext : (c : C) → C-sym (C-sym c) ≡ c
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
            → Maybe (D C t ty) → List C
  conflicts nothing  = []
  conflicts (just p) = forget p
\end{code}
%</conflicts>

%<*conflictsμ>
\begin{code}
  conflictsμ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            → Maybe (List (Dμ C t ty)) → List C
  conflictsμ nothing  = []
  conflictsμ (just p) = forgetμ p
\end{code}
%</conflictsμ>
