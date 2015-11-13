\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff
open import Diffing.Patches.Diff.Correctness
open import Diffing.Patches.Residual

open import Relation.Binary.PropositionalEquality

module Diffing.Patches.Alignment where
\end{code}

          Alignment
  ============================

  An important notion is the notion of alignment. Two patches
  are said to be aligned if and only if they are defined for the same inputs.

  For instance, Alice and Bob edit a file O, then their patches
  are aligned as applying any of them to O is well-defined.

  The main usefullness of alignment is to be able to perform induction
  on two compatible patches at the same time. For instance,
  for defining a residual patch, we require the two patches to be aligned, as
  it makes no sense to define the residual of two patches that can't be applied
  to the same object.

  Now we can finaly define alignment.

%<*Aligned-def>
\begin{code}
  Aligned : {n : ℕ}{t : Tel n}{ty : U n}
          → D t ty → D t ty → Set
  Aligned {n} {t} {ty} d1 d2 
    = (x : ElU ty t) → Is-Just (gapply d1 x) iff Is-Just (gapply d2 x) 
\end{code}
%</Aligned-def>

%<*Aligned*-def>
\begin{code}
  Aligned*For : {n : ℕ}{t : Tel n}{ty : U (suc n)}
              → List (Dμ t ty) → ElU (μ ty) t → Set
  Aligned*For {n} {t} {ty} dx x
    = Σ (ElU (μ ty) t × List (ElU (μ ty) t))
        (λ e → gapplyL dx (x ∷ []) ≡ just (p1 e ∷ p2 e))

  Aligned* : {n : ℕ}{t : Tel n}{ty : U (suc n)}
          → List (Dμ t ty) → List (Dμ t ty) → Set
  Aligned* {n} {t} {ty} d1 d2 
    = (x : ElU (μ ty) t)
    → Aligned*For d1 x iff Aligned*For d2 x
\end{code}
%</Aligned*-def>

We need to convert between both notions.

\begin{code}
  open import Diffing.Utils.Monads
  open Monad {{...}}

  sh-lemma : {A : Set}{x : List A}
           → Is-Just (safeHead x) 
           → Σ (A × List A) (λ r → x ≡ p1 r ∷ p2 r) 
  sh-lemma j = {!!}

  AtoA* : {n : ℕ}{t : Tel n}{ty : U (suc n)}
        → (d1 d2 : List (Dμ t ty))
        → Aligned (D-mu d1) (D-mu d2)
        → Aligned* d1 d2
  AtoA* d1 d2 a x with a x
  ...| a1 , a2 with gapplyL d2 (x ∷ []) | gapplyL d1 (x ∷ [])
  ...| just [] | nothing = {!id , id!}
  ...| just _  | nothing = {!⊥-elim (Is-Just-⊥ ?)!}
  ...| nothing | just k2 = {!!}
  ...| nothing | nothing = {!!}
  ...| just k1 | just k2 = {!!}

  A*toA : {n : ℕ}{t : Tel n}{ty : U (suc n)}
        → (d1 d2 : List (Dμ t ty))
        → Aligned* d1 d2
        → Aligned (D-mu d1) (D-mu d2)
  A*toA d1 d2 a = {!!}

  <C>-strip : {A B : Set}{f : A → B}
              {x : Maybe (A ⊎ C)}
            → Is-Just (f <C> x)
            → Is-Just x
  <C>-strip {x = nothing} ()
  <C>-strip {x = just x} _ = indeed x

  <$>-build : {A B : Set}{f : A → B}
              {x : Maybe A}
            → Is-Just x
            → Is-Just (f <$>+1 x)
  <$>-build {f = f} (indeed x) = indeed (f x)

  <$>-iff : {A B : Set}{f : A → B}
            {x y : Maybe A}
          → Is-Just x iff Is-Just y
          → Is-Just (f <$>+1 x) iff Is-Just (f <$>+1 y)
  <$>-iff {f = f} {x = just x} {just y} (a1 , a2) 
    = (<$>-build {f = f} ∘ a1 ∘ <$>-build) 
    , (<$>-build {f = f} ∘ a2 ∘ <$>-build)
  <$>-iff {x = just x} {nothing} (a1 , a2) 
    = ⊥-elim (Is-Just-⊥ a1)
  <$>-iff {x = nothing} {just x} (a1 , a2)
    = ⊥-elim (Is-Just-⊥ a2)
  <$>-iff {x = nothing} {nothing} (a1 , a2) 
    = id , id
              

  aligned-inl : {n : ℕ}{t : Tel n}{ty ty' : U n}
                {d1 d2 : D t ty}
              → Aligned d1 d2
              → Aligned (D-inl {b = ty'} d1) (D-inl d2)
  aligned-inl a (inl x) = <$>-iff {f = inl} (a x)
  aligned-inl a (inr x) = id , id
\end{code}

%<*residual-aligned>
\begin{code}
  /-aligned : {n : ℕ}{t : Tel n}{ty : U n}
            → (d1 d2 : D t ty)
            → Is-Just (d1 / d2)
            → Aligned d1 d2
\end{code}
%</residual-aligned>
\begin{code}
  /-aligned {ty = u1} D-void D-void prf void = id , id
  /-aligned {ty = a ⊕ b} (D-inl d1) (D-inl d2) prf
    = aligned-inl (/-aligned d1 d2 (<C>-strip prf))
  /-aligned {ty = a ⊕ b} (D-inl d1) (D-setl x x₁) prf x₂ = {!!}
  /-aligned {ty = a ⊕ b} (D-inl d1) (D-inr d2) () x
  /-aligned {ty = a ⊕ b} (D-inl d1) (D-setr x x₁) () x₂
  /-aligned {ty = a ⊕ b} (D-inr d1) d2 prf x = {!!}
  /-aligned {ty = a ⊕ b} (D-setl x x₁) d2 prf x₂ = {!!}
  /-aligned {ty = a ⊕ b} (D-setr x x₁) d2 prf x₂ = {!!}
  /-aligned {ty = a ⊗ b} (D-pair da da') (D-pair db db') prf x = {!!}
  /-aligned {ty = β F a} d1 d2 prf x = {!!}
  /-aligned {ty = vl} d1 d2 prf x = {!!}
  /-aligned {ty = wk ty} d1 d2 prf x = {!!} 
  /-aligned {ty = μ ty} (D-mu d1) (D-mu d2) prf x₂ = {!!}
    where
      /-aligned* : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            → (d1 d2 : List (Dμ t ty))
            → Is-Just (res d1 d2)
            → Aligned* d1 d2
      /-aligned* = {!!}
\end{code}
