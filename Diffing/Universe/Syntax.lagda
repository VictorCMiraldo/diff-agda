\begin{code}
open import Prelude
open import Level renaming (zero to lz; suc to ls)
open import Data.Nat.Properties.Simple using (+-comm)

module Diffing.Universe.Syntax where
\end{code}

This universe and it's semantics were adapted from:
   "Generic Programming with Dependent Types"
from McBride, Altenkirch and Morris.

Our difference is using Fin's to represent variables,
as these allow an easier syntatical handling of terms of U.

%<*U-def>
\begin{code}
  data U : ℕ → Set where
    u0  : {n : ℕ} → U n
    u1  : {n : ℕ} → U n
    _⊕_ : {n : ℕ} → U n → U n → U n
    _⊗_ : {n : ℕ} → U n → U n → U n
    β   : {n : ℕ} → U (suc n) → U n → U n
    μ   : {n : ℕ} → U (suc n) → U n
    vl  : {n : ℕ} → U (suc n)
    wk  : {n : ℕ} → U n → U (suc n)
\end{code}
%</U-def>

\begin{code}
  infixr 20 _⊕_
  infixr 25 _⊗_
\end{code}

%<*wk-star>
\begin{code}
  {-# TERMINATING #-}
  wk* : {n : ℕ}(m : ℕ) → U n → U (n + m)
  wk* {n} m a rewrite +-comm n m with m
  ...| zero  = a
  ...| suc k = wk (subst U (+-comm n k) (wk* k a))
\end{code}
%</wk-star>

%<*Tel-def>
\begin{code}
  data Tel : ℕ → Set where
    tnil  : Tel 0
    tcons : {n : ℕ} → U n → Tel n → Tel (suc n)
\end{code}
%</Tel-def>

%<*tel-lkup>
\begin{code}
  tel-lkup : {n : ℕ} → Fin n → Tel n → U n
  tel-lkup {zero} () t
  tel-lkup {suc n} fz (tcons x t) = wk x
  tel-lkup {suc n} (fs i) (tcons x t) = wk (tel-lkup i t)
\end{code}
%</tel-lkup>

%<*tel-forget>
\begin{code}
  tel-forget : {n : ℕ} → Fin n → Tel n → Tel n
  tel-forget {zero} () tnil
  tel-forget {suc n} fz (tcons x t)     = tcons u1 t
  tel-forget {suc n} (fs i) (tcons x t) = tcons x (tel-forget i t)
\end{code}
%</tel-forget>

Now, we define a 'free-monad' like datatype for elements.

%<*ElU-def>
\begin{code}
  data ElU : {n : ℕ} → U n → Tel n → Set where
    void : {n : ℕ}{t : Tel n} → ElU u1 t
    inl  : {n : ℕ}{t : Tel n}{a b : U n}(x : ElU a t) → ElU (a ⊕ b) t
    inr  : {n : ℕ}{t : Tel n}{a b : U n}(x : ElU b t) → ElU (a ⊕ b) t
    _,_  : {n : ℕ}{t : Tel n}{a b : U n} → ElU a t → ElU b t → ElU (a ⊗ b) t
    top  : {n : ℕ}{t : Tel n}{a : U n}   → ElU a t → ElU vl (tcons a t)
    pop  : {n : ℕ}{t : Tel n}{a b : U n} → ElU b t → ElU (wk b) (tcons a t)
    mu   : {n : ℕ}{t : Tel n}{a : U (suc n)} → ElU a (tcons (μ a) t) → ElU (μ a) t
    red  : {n : ℕ}{t : Tel n}{F : U (suc n)}{x : U n}
         → ElU F (tcons x t)
         → ElU (β F x) t
\end{code}
%</ElU-def>

It is handy to state that ElU constructors
are injections.

\begin{code}
  inj-inl : {n : ℕ}{t : Tel n}{a b : U n}{x y : ElU a t} 
          → inl {n} {t} {a} {b} x ≡ inl y → x ≡ y
  inj-inl refl = refl

  inj-inr : {n : ℕ}{t : Tel n}{a b : U n}{x y : ElU b t} 
          → inr {n} {t} {a} {b} x ≡ inr y → x ≡ y
  inj-inr refl = refl

  inj-, : {n : ℕ}{t : Tel n}{a b : U n}{xa ya : ElU a t}{xb yb : ElU b t}
        → _≡_ {a = lz} {A = ElU (a ⊗ b) t} (_,_ {n} {t} {a} {b} xa xb) (ya , yb) 
        → (xa ≡ ya × xb ≡ yb)
  inj-, refl = refl , refl

  inj-top : {n : ℕ}{t : Tel n}{a : U n}{x y : ElU a t}
          → top {n} {t} {a} x ≡ top y → x ≡ y
  inj-top refl = refl

  inj-pop : {n : ℕ}{t : Tel n}{a b : U n}{x y : ElU b t}
          → pop {n} {t} {a} {b} x ≡ pop y → x ≡ y
  inj-pop refl = refl

  inj-mu : {n : ℕ}{t : Tel n}{a : U (suc n)}{x y : ElU a (tcons (μ a) t)}
         → mu {n} {t} {a} x ≡ mu y → x ≡ y
  inj-mu refl = refl

  inj-red : {n : ℕ}{t : Tel n}{F : U (suc n)}{x : U n}{a b : ElU F (tcons x t)}
           → red {n} {t} {F} {x} a ≡ red b
           → a ≡ b
  inj-red refl = refl
\end{code}

And some general purpose functions

\begin{code}
  unpop : {n : ℕ}{t : Tel n}{x : U n}{a : U n}
        → ElU (wk a) (tcons x t) → ElU a t
  unpop (pop el) = el
\end{code}


%<*U-example>
\begin{code}
  list : {n : ℕ} → U (suc n)
  list = μ (u1 ⊕ wk vl ⊗ vl)

  myList : {n : ℕ}{t : Tel n} → ElU list (tcons u1 t)
  myList = mu (inr (pop (top void) , top (mu (inl void))))
\end{code}
%</U-example>
