\begin{code}
open import Prelude
open import Level renaming (zero to lz; suc to ls)
open import Data.Nat using (_≤_; s≤s; z≤n)
open import Diffing.Utils.Propositions
  using (LEQ; LEQ-refl; LEQ-step; ≤-LEQ; LEQ-≤)


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
  wk* : {n m : ℕ} → LEQ m n → U m → U n
  wk* LEQ-refl a       = a
  wk* (LEQ-step prf) a = wk (wk* prf a)
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

We can always substitute something in a telescope,
as long as we use the correct number of variables.

%<*tel-subst>
\begin{code}
  tel-subst : {n m : ℕ} → LEQ (suc m) n → U m → Tel n → Tel n
  tel-subst prf a tnil                   = tnil
  tel-subst LEQ-refl       a (tcons x t) = tcons a t
  tel-subst (LEQ-step prf) a (tcons x t) = tcons x (tel-subst prf a t)        
\end{code}
%</tel-subst>

A telescope restriction is also important, as we might want
to use just a subtelescope of t.

%<*tel-drop>
\begin{code}
  tel-drop : {n m : ℕ} → LEQ m n → Tel n → Tel m
  tel-drop LEQ-refl t               = t
  tel-drop (LEQ-step p) (tcons _ t) = tel-drop p t
\end{code}
%</tel-drop>

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

%<*countU>
\begin{code}
  countU : {n : ℕ} → Fin n → U n → ℕ
  countU i u1 = 0
  countU i (a ⊕ b) = countU i a + countU i b
  countU i (a ⊗ b) = countU i a + countU i b
  countU i (β F x) = countU i x + countU (fs i) F
  countU i (μ u) = countU (fs i) u
  countU fz vl = 1
  countU (fs i) vl = 0
  countU fz (wk u) = 0
  countU (fs i) (wk u) = countU i u
\end{code}
%</countU>

%<*sizeU>
\begin{code}
  sizeU : {n : ℕ} → U n → ℕ
  sizeU u1 = 1
  sizeU (a ⊕ b) = sizeU a + sizeU b
  sizeU (a ⊗ b) = sizeU a * sizeU b
  sizeU (β F x) = sizeU x * countU fz F + sizeU F
  sizeU (μ u) = sizeU u
  sizeU vl = 1
  sizeU (wk u) = sizeU u
\end{code}
%</sizeU>

%<*sizeEl>
\begin{code}
  sizeElU : {n : ℕ}{t : Tel n}{u : U n} → ElU u t → ℕ
  sizeElU void = 1
  sizeElU (inl el) = sizeElU el
  sizeElU (inr el) = sizeElU el
  sizeElU (ela , elb) = sizeElU ela + sizeElU elb
  sizeElU (top el) = sizeElU el
  sizeElU (pop el) = sizeElU el
  sizeElU (mu el) = 1 + sizeElU el
  sizeElU (red el) = sizeElU el
\end{code}
%</sizeEl>
