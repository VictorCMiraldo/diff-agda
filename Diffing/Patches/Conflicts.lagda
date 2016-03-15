\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Patches.Diff
open import Diffing.Patches.Diff.Functor 
  using (forget; forgetμ; ↓_; cast; castμ)

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
           → ElU (a ⊕ b) t → ElU (a ⊕ b) t → ElU (a ⊕ b) t 
           → C t (a ⊕ b)
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
  IsGrow : {n : ℕ}{t : Tel n}{ty : U n} → C t ty → Set
  IsGrow (GrowL _)    = Unit
  IsGrow (GrowR _)    = Unit
  IsGrow (GrowLR _ _) = Unit
  IsGrow _ = ⊥

  IsGrow? : {n : ℕ}{t : Tel n}{ty : U n}(c : C t ty) → Dec (IsGrow c)
  IsGrow? (UpdUpd x x₁ x₂) = no id
  IsGrow? (DelUpd x x₁) = no id
  IsGrow? (UpdDel x x₁) = no id
  IsGrow? (GrowL x) = yes unit
  IsGrow? (GrowLR x x₁) = yes unit
  IsGrow? (GrowR x) = yes unit
\end{code}
%</IsGrow>

%<*IsUpd>
\begin{code}
  IsUpd : {n : ℕ}{t : Tel n}{ty : U n} → C t ty → Set
  IsUpd (UpdUpd _ _ _) = Unit
  IsUpd (UpdDel _ _)   = Unit
  IsUpd (DelUpd _ _)   = Unit
  IsUpd _ = ⊥

  IsUpd? : {n : ℕ}{t : Tel n}{ty : U n}(c : C t ty) → Dec (IsUpd c)
  IsUpd? (UpdUpd x x₁ x₂) = yes unit
  IsUpd? (DelUpd x x₁) = yes unit
  IsUpd? (UpdDel x x₁) = yes unit
  IsUpd? (GrowL x) = no (λ z → z)
  IsUpd? (GrowLR x x₁) = no (λ z → z)
  IsUpd? (GrowR x) = no (λ z → z)
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
            → Maybe (D C t ty) → List (↓ C)
  conflicts nothing  = []
  conflicts (just p) = forget p
\end{code}
%</conflicts>

%<*conflictsμ>
\begin{code}
  conflictsμ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            → Maybe (List (Dμ C t ty)) → List (↓ C)
  conflictsμ nothing  = []
  conflictsμ (just p) = forgetμ p
\end{code}
%</conflictsμ>

  And an indexed type for possible solved conflicts.

%<*Fewer>
\begin{code}
  Fewer : ∀{a}(A : {n : ℕ} → Tel n → U n → Set a)
         → {n : ℕ} → Tel n → U n → Set a
  Fewer A t ty = D ⊥ₚ t ty ⊎ A t ty
\end{code}
%</Fewer>

  Now, we can "absorb" a fewer.

%<*partial-merge>
\begin{code}
  partial-merge : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}
                  {A : {n : ℕ} → Tel n → U n → Set a}
                → D (Fewer A) t ty → D A t ty
  partial-merge = aux
    where
      mutual
        aux : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}
               {A : {n : ℕ} → Tel n → U n → Set a}
            → D (Fewer A) t ty → D A t ty
        aux (D-A (i1 x)) = cast x
        aux (D-A (i2 y)) = D-A y
        aux D-unit = D-unit
        aux (D-inl d) = D-inl (aux d)
        aux (D-inr d) = D-inr (aux d)
        aux (D-setl x x₁) = D-setl x x₁
        aux (D-setr x x₁) = D-setr x x₁
        aux (D-pair d d₁) = D-pair (aux d) (aux d₁)
        aux (D-mu x) = D-mu (aux* x)
        aux (D-def d) = D-def (aux d)
        aux (D-top d) = D-top (aux d)
        aux (D-pop d) = D-pop (aux d)

        aux* : ∀{a}{n : ℕ}{t : Tel n}{ty : U (suc n)}
               {A : {n : ℕ} → Tel n → U n → Set a}
             → List (Dμ (Fewer A) t ty) → List (Dμ A t ty)
        aux* [] = []
        aux* (Dμ-A (i1 (D-A ())) ∷ ls)
        aux* (Dμ-A (i1 (D-mu x)) ∷ ls) = castμ x ++ aux* ls
        aux* (Dμ-A (i2 y) ∷ ls) = Dμ-A y ∷ aux* ls
        aux* (Dμ-ins x ∷ ls) = Dμ-ins x ∷ aux* ls
        aux* (Dμ-del x ∷ ls) = Dμ-del x ∷ aux* ls
        aux* (Dμ-dwn dx ∷ ls) = Dμ-dwn (aux dx) ∷ aux* ls
    
\end{code}
%</partial-merge>
