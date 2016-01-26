\begin{code}
open import Prelude
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties.Simple

open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.Ops
open import Diffing.Universe.MuUtils
open import Diffing.Universe.Measures
open import Diffing.Patches.Diff
open import Diffing.Utils.Propositions using (nat-≤-step)

module Diffing.Universe.SOP where
\end{code}

  In order to speak about the cost of a diff, and prove properties
  about it, it is important to consider types which are sums-of-products
  from the rest.

  We'll now introduce the universe of Haskell ADT types. They correspond too
  the following "grammar":

\begin{code} 
  mutual
    data PROD : {n : ℕ} → U n → Set where
      IsProd : {n : ℕ}{a b : U n} → PROD a → PROD b → PROD (a ⊗ b)
      IsNil  : {n : ℕ}            → PROD {n} u1
      IsVl   : {n : ℕ}            → PROD {suc n} vl
      IsWk   : {n : ℕ}{a : U n}   → PROD a → PROD {suc n} (wk a) 

    data SUM : {n : ℕ} → U n → Set where
      IsSum  : {n : ℕ}{a b : U n} → SUM a → SUM b → SUM (a ⊕ b)
      IsProd : {n : ℕ}{a : U n}   → PROD a → SUM a 
      IsNil  : {n : ℕ} → SUM {n} u0

  data Haskell : {n : ℕ} → U n → Set where
    IsMu  : {n : ℕ}{a : U (suc n)} → Haskell a → Haskell (μ a)
    IsApp : {n : ℕ}{a : U (suc n)}{b : U n}
          → Haskell a → Haskell b → Haskell (β a b)
    IsSOP : {n : ℕ}{a : U n} → SUM a → Haskell a

  data HTel : ℕ → Set where
    htnil  : HTel 0
    htcons : {n : ℕ} → Σ (U n) Haskell → HTel n → HTel (suc n)

  toTel : {n : ℕ} → HTel n → Tel n
  toTel htnil               = tnil
  toTel (htcons (ty , _) t) = tcons ty (toTel t)
\end{code}

\begin{code}
  SameFactor : {n : ℕ}{t t' : Tel n}{ty : U n}
             → SUM ty 
             → (a : ElU ty t)
             → (b : ElU ty t')
             → Set
  SameFactor (IsSum sa sb) (inl a) (inl b) = SameFactor sa a b
  SameFactor (IsSum sa sb) (inl a) (inr b) = ⊥
  SameFactor (IsSum sa sb) (inr a) (inl b) = ⊥
  SameFactor (IsSum sa sb) (inr a) (inr b) = SameFactor sb a b
  SameFactor (IsProd x) a b = Unit
  SameFactor IsNil a b      = Unit

  SameCons : {n : ℕ}{t t' : Tel n}{ty : U n}
           → Haskell ty
           → (a : ElU ty t)
           → (b : ElU ty t')
           → Set
  SameCons (IsMu x) (mu a) (mu b)      = SameCons x a b
  SameCons (IsApp F _) (red a) (red b) = SameCons F a b
  SameCons (IsSOP x) a b               = SameFactor x a b
\end{code}

\begin{code}
  SF-refl : {n : ℕ}{t : Tel n}{ty : U n}
         → (h : SUM ty)
         → (a : ElU ty t)
         → SameFactor h a a
  SF-refl (IsSum ha hb) (inl a) = SF-refl ha a
  SF-refl (IsSum ha hb) (inr b) = SF-refl hb b
  SF-refl (IsProd x) a = unit
  SF-refl IsNil a = unit

  SC-refl : {n : ℕ}{t : Tel n}{ty : U n}
         → (h : Haskell ty)
         → (a : ElU ty t)
         → SameCons h a a
  SC-refl (IsMu h) (mu a) = SC-refl h a
  SC-refl (IsApp Fh _) (red a) = SC-refl Fh a
  SC-refl (IsSOP x) a = SF-refl x a
\end{code}
  

\begin{code}
  SF-comm : {n : ℕ}{t t' : Tel n}{ty : U n}
         → (h : SUM ty)
         → (a : ElU ty t)
         → (b : ElU ty t')
         → SameFactor h a b
         → SameFactor h b a
  SF-comm (IsSum ha hb) (inl a) (inl b) prf = SF-comm ha a b prf
  SF-comm (IsSum ha hb) (inl a) (inr b) ()
  SF-comm (IsSum ha hb) (inr a) (inl b) ()
  SF-comm (IsSum ha hb) (inr a) (inr b) prf = SF-comm hb a b prf
  SF-comm (IsProd x) a b prf = unit
  SF-comm IsNil a b prf = unit

  SC-comm : {n : ℕ}{t t' : Tel n}{ty : U n}
         → (h : Haskell ty)
         → (a : ElU ty t)
         → (b : ElU ty t')
         → SameCons h a b
         → SameCons h b a
  SC-comm (IsMu h) (mu a) (mu b) prf = SC-comm h a b prf
  SC-comm (IsApp Fh _) (red a) (red b) prf = SC-comm Fh a b prf
  SC-comm (IsSOP x) a b prf = SF-comm x a b prf
\end{code}

\begin{code}
  SF-trans : {n : ℕ}{t t' t'' : Tel n}{ty : U n}
         → (h : SUM ty)
         → (a : ElU ty t)
         → (b : ElU ty t')
         → (c : ElU ty t'')
         → SameFactor h a b
         → SameFactor h b c
         → SameFactor h a c
  SF-trans (IsSum ha hb) (inl a) (inl b) (inl c) q1 q2 = SF-trans ha a b c q1 q2
  SF-trans (IsSum ha hb) (inl a) (inl b) (inr c) q1 ()
  SF-trans (IsSum ha hb) (inl a) (inr b) (inl c) () q2
  SF-trans (IsSum ha hb) (inl a) (inr b) (inr c) () q2 
  SF-trans (IsSum ha hb) (inr a) (inl b) (inl c) () q2 
  SF-trans (IsSum ha hb) (inr a) (inl b) (inr c) () q2 
  SF-trans (IsSum ha hb) (inr a) (inr b) (inl c) q1 () 
  SF-trans (IsSum ha hb) (inr a) (inr b) (inr c) q1 q2 = SF-trans hb a b c q1 q2
  SF-trans (IsProd x) a b c q1 q2 = unit
  SF-trans IsNil a b c q1 q2 = unit

  SC-trans : {n : ℕ}{t t' t'' : Tel n}{ty : U n}
         → (h : Haskell ty)
         → (a : ElU ty t)
         → (b : ElU ty t')
         → (c : ElU ty t'')
         → SameCons h a b
         → SameCons h b c
         → SameCons h a c
  SC-trans (IsMu h) (mu a) (mu b) (mu c) q1 q2 = SC-trans h a b c q1 q2
  SC-trans (IsApp Fh _) (red a) (red b) (red c) q1 q2 = SC-trans Fh a b c q1 q2
  SC-trans (IsSOP x) a b c q1 q2 = SF-trans x a b c q1 q2
\end{code}

Ignoring arguments doesn't change the constructor.

\begin{code}
  forget-factor : {n : ℕ}{t : Tel n}{ty : U n}{i : Fin n}
            → (h : SUM ty)
            → (a : ElU ty t)
            → SameFactor h a (forget i a)
  forget-factor (IsSum ha hb) (inl a) = forget-factor ha a
  forget-factor (IsSum ha hb) (inr b) = forget-factor hb b
  forget-factor (IsProd x) a = unit
  forget-factor IsNil a = unit

  forget-cons : {n : ℕ}{t : Tel n}{ty : U n}{i : Fin n}
            → (h : Haskell ty)
            → (a : ElU ty t)
            → SameCons h a (forget i a)
  forget-cons (IsMu h) (mu a)       = forget-cons h a
  forget-cons (IsApp Fh h ) (red a) = forget-cons Fh a
  forget-cons (IsSOP h) a           = forget-factor h a

  μ-hd-factor : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            → (h : SUM ty)
            → (a : ElU ty (tcons (μ ty) t))
            → SameFactor h a (μ-hd (mu a))
  μ-hd-factor (IsSum ha hb) (inl a) = forget-factor ha a
  μ-hd-factor (IsSum ha hb) (inr b) = forget-factor hb b
  μ-hd-factor (IsProd x) a = unit
  μ-hd-factor IsNil a = unit

  μ-hd-cons : {n : ℕ}{t : Tel n}{ty : U (suc n)}
            → (h : Haskell ty)
            → (a : ElU ty (tcons (μ ty) t))
            → SameCons h a (μ-hd (mu a))
  μ-hd-cons (IsMu h) (mu a) = forget-cons h a
  μ-hd-cons (IsApp h h₁) (red a) = forget-cons h a
  μ-hd-cons (IsSOP x) a = μ-hd-factor x a
\end{code}

\begin{code}
  μ-hd-cons₂ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
             → (h : Haskell ty)
             → (a b : ElU (μ ty) t)
             → SameCons (IsMu h) a b
             → SameCons h (μ-hd a) (μ-hd b)
  μ-hd-cons₂ h (mu a) (mu b) hip
    = SC-comm h (μ-hd (mu b)) (μ-hd (mu a)) 
      (SC-trans h (μ-hd (mu b)) a (μ-hd (mu a)) 
        (SC-comm h a (μ-hd (mu b)) 
          (SC-trans h a b (μ-hd (mu b)) hip (μ-hd-cons h b))) 
        (μ-hd-cons h a))
\end{code}

begin{code}
  tag-list : {n : ℕ} → U (2 + n)
  tag-list = μ (u1 ⊕ (wk vl) ⊕ (vl ⊗ wk vl))

  bool : {n : ℕ} → U n
  bool = u1 ⊕ u1

  list : {n : ℕ} → U (suc n)
  list = μ (u1 ⊕ wk vl ⊗ vl)

  nohask : {n : ℕ} → U (suc n)
  nohask = μ (u1 ⊕ (wk vl ⊗ (vl ⊕ vl)))

  bl : {n : ℕ} → U (suc n)
  bl = β (β tag-list bool) (β list bool)

  prf : {n : ℕ} → Haskell {suc n} bl
  prf = IsApp (IsApp (IsMu (IsSOP {!!})) {!!}) {!!}

  prf2 : {n : ℕ} → Haskell {suc n} nohask → ⊥
  prf2 (IsMu (IsSOP (IsSum (IsProd x) (IsProd (IsProd x₁ ())))))
  prf2 (IsMu (IsSOP (IsProd ())))
  prf2 (IsSOP (IsProd ()))
  
end{code}
