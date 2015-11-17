\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Patches.Diff

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
  data C : Set where
    UpdUpd : {n : ℕ}{t : Tel n}{a b : U n}
           → ElU a t → ElU b t → C
    DelUpd : {n : ℕ}{t : Tel n}{a b : U n}
           → ElU a t → ElU b t → C
    UpdDel : {n : ℕ}{t : Tel n}{a b : U n}
           → ElU a t → ElU b t → C
    GrowL  : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → ValU a t → C
    GrowLR : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → ValU a t → ValU a t → C
    GrowR  : {n : ℕ}{t : Tel n}{a : U (suc n)}
           → ValU a t → C
\end{code}
%</C-def>

  An important observation is that conflicts are symmetric:

%<*C-sym>
\begin{code}
  C-sym : C → C
  C-sym (UpdUpd x y) = UpdUpd y x
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
      ext (UpdUpd x y) = refl
      ext (DelUpd x y) = refl
      ext (UpdDel x y) = refl
      ext (GrowL x)    = refl
      ext (GrowLR x y) = refl
      ext (GrowR x)    = refl
\end{code}

