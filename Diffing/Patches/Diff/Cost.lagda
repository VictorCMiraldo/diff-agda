\begin{code}
open import Prelude
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties.Simple

open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.Ops
open import Diffing.Universe.MuUtils
open import Diffing.Universe.Measures
open import Diffing.Patches.Diff.D
open import Diffing.Utils.Propositions 
  using (nat-≤-step; ≤-+; nat-≤-elim2; ¬≤; nat-≤-abs; 
         ≤-pi; nat-≤-elim; nat-≤-unstep; ≤-trans; nat-≤-strict;
         nat-≤-dec)

module Diffing.Patches.Diff.Cost where
\end{code}


  The cost function is trivial for the non-inductive types.
  The inductive types are a bit trickier, though.
  We want our diff to have maximum sharing, that means
  we seek to copy most of the information we see.
  However, there are two obvious ways of copying:

    (D-mu-cpy x d) ∨ (D-mu-down (diff x x) d)

  We want the first one to be chosen.
  Which means, 
  
    cost (D-mu-cpy x d) < cost (D-mu-down (diff x x) d)
  ↔         k + cost d  < cost (diff x x) + 1 + cost d
  ⇐                  k  < cost (diff x x) + 1
  
  However, diff x x will basically be copying every constructor of x,
  which is intuitively the size of x. We then define the cost of
  copying x to be 0.

  Inserting and deleting, on the other hand, must be more
  expensive than making structural changes (when possible!)
  The same reasoning applies to the fact that we prefer copying
  over inserting and deleting.

    D-mu-cpy x d ≈ D-mu-down (diff x x) d ≈ D-mu-ins x (D-mu-del x d)
  
  With this in mind, we implement the cost function as follows:

\begin{code}
  sum : ∀{a}{A : Set a}(f : A → ℕ)
      → List A → ℕ
  sum f = foldr (λ h r → f h + r) 0

  mutual
    {-# TERMINATING #-}
\end{code}
%<*cost-def>
\begin{code}
    cost : {n : ℕ}{t : Tel n}{ty : U n} → Patch t ty → ℕ
    cost (D-A ())
    cost  D-void        = 0
    cost (D-inl d)      = cost d
    cost (D-inr d)      = cost d
    cost (D-setl xa xb) = 2 * (sizeElU xa + sizeElU xb)
    cost (D-setr xa xb) = 2 * (sizeElU xa + sizeElU xb)
    cost (D-pair da db) = cost da + cost db
    cost (D-β d)   = cost d
    cost (D-top d) = cost d
    cost (D-pop d) = cost d
    cost (D-mu l)  = costL l

    costL : {n : ℕ}{t : Tel n}{ty : U (suc n)} → Patchμ t ty → ℕ
    costL = sum costμ

    costμ : {n : ℕ}{t : Tel n}{ty : U (suc n)} → Dμ (const (const ⊥)) t ty → ℕ
    costμ (Dμ-A ())
    costμ (Dμ-ins x) = 1 + sizeElU x
    costμ (Dμ-del x) = 1 + sizeElU x
    costμ (Dμ-dwn x) = cost x
\end{code}
%</cost-def>

\begin{code}
  infixr 20 _⊔_
  infixr 20 _⊔μ_
\end{code}

%<*lub-def>
\begin{code}
  _⊔_ : {n : ℕ}{t : Tel n}{ty : U n}
      → Patch t ty → Patch t ty → Patch t ty
  _⊔_ {ty = ty} da db with cost da ≤?-ℕ cost db
  ...| yes _ = da
  ...| no  _ = db
\end{code}
%</lub-def>

\begin{code}
  data Ord : ℕ → ℕ → Set where
    LE : ∀{m n} → suc m ≤ n → Ord m n
    GE : ∀{m n} → suc n ≤ m → Ord m n
    EQ : ∀{m n} → m ≡ n → Ord m n

  comp : (n m : ℕ) → Ord n m
  comp n m with n ≟-ℕ m
  ...| yes p = EQ p
  ...| no ¬p with n ≤?-ℕ m
  ...| yes q = LE (nat-≤-elim2 q ¬p)
  ...| no ¬q = GE (nat-≤-elim2 (¬≤ ¬q) (¬p ∘ sym))

  comp-LE : {m n : ℕ}(p : suc m ≤ n)
          → comp m n ≡ LE p
  comp-LE {m} {n} p with m ≟-ℕ n 
  ...| yes q = ⊥-elim (nat-≤-abs p q)
  ...| no ¬q with m ≤?-ℕ n
  ...| yes j = cong LE (≤-pi (nat-≤-elim2 j ¬q) p)
  ...| no  j = ⊥-elim (j (nat-≤-unstep p))

  comp-GE : {m n : ℕ}(p : suc n ≤ m)
          → comp m n ≡ GE p
  comp-GE {m} {n} p with m ≟-ℕ n 
  ...| yes q = ⊥-elim (nat-≤-abs p (sym q))
  ...| no ¬q with m ≤?-ℕ n
  ...| yes j = ⊥-elim (nat-≤-abs (≤-trans p j) refl)
  ...| no  j = cong GE (≤-pi (nat-≤-elim2 (¬≤ j) (λ z → ¬q (sym z))) p)

  comp-EQ : {n m : ℕ}(p : n ≡ m)
          → comp n m ≡ EQ p
  comp-EQ {n} {m} hip with n ≟-ℕ m
  ...| yes p  = cong EQ (≡-pi p hip)
  ...| no  ¬p = ⊥-elim (¬p hip)

  comp-NEQ : {n m : ℕ}{q : ¬ (n ≡ m)}(p : suc n ≤ m)
           → (n ≟-ℕ m) ≡ no q
  comp-NEQ {n} {m} {q} p with n ≟-ℕ m
  ...| yes z = ⊥-elim (nat-≤-abs p z)
  ...| no ¬z = cong no (¬≡-pi ¬z q)
\end{code}

\begin{code}
  Patchμ1 : {n : ℕ}(t : Tel n)(ty : U (suc n)) → Set
  Patchμ1 t ty = Dμ ⊥ₚ t ty × Patchμ t ty

  {-# TERMINATING #-}
  bias : {n : ℕ}{t : Tel n}{ty : U (suc n)}
       → Patchμ1 t ty → Patchμ1 t ty → Set
  bias (p , []) (q , []) 
    = suc (costμ p) ≤ costμ q
  bias (p , (hp ∷ ps)) (q , []) 
    = suc (costμ p) ≤ costμ q
  bias (p , []) (q , (hq ∷ qs)) 
    = suc (costμ p) ≤ costμ q
  bias (p , (hp ∷ ps)) (q , (hq ∷ qs)) 
       = suc (costμ p) ≤ costμ q 
       ⊎ costμ p ≡ costμ q × bias (hp , ps) (hq , qs)

  {-# TERMINATING #-}
  bias-dec : {n : ℕ}{t : Tel n}{ty : U (suc n)}
           → (p q : Patchμ1 t ty) → Dec (bias p q)
  bias-dec (p , []) (q , [])        = suc (costμ p) ≤?-ℕ costμ q
  bias-dec (p , []) (q , (hq ∷ qs)) = suc (costμ p) ≤?-ℕ costμ q
  bias-dec (p , (hp ∷ ps)) (q , []) = suc (costμ p) ≤?-ℕ costμ q
  bias-dec (p , (hp ∷ ps)) (q , (hq ∷ qs)) with bias-dec (hp , ps) (hq , qs)
  bias-dec (p , (hp ∷ ps)) (q , (hq ∷ qs)) | yes r with costμ p ≟-ℕ costμ q
  ...| yes c = yes (i2 (c , r))
  ...| no ¬c with suc (costμ p) ≤?-ℕ costμ q
  ...| yes d = yes (i1 d)
  ...| no ¬d = no (either ¬d (¬c ∘ p1))
  bias-dec (p , (hp ∷ ps)) (q , (hq ∷ qs)) | no ¬r with suc (costμ p) ≤?-ℕ (costμ q)
  ...| yes d = yes (i1 d)
  ...| no ¬d = no (either ¬d (¬r ∘ p2))
  
  bias-antisym : {n : ℕ}{t : Tel n}{ty : U (suc n)}
               → (p q : Patchμ1 t ty) → bias p q → ¬ (bias q p)
  bias-antisym (p , []) (q , []) hip abs 
    = nat-≤-abs (≤-trans hip (nat-≤-unstep abs)) refl
  bias-antisym (p , []) (q , hq ∷ qs) hip abs
    = nat-≤-abs (≤-trans hip (nat-≤-unstep abs)) refl
  bias-antisym (p , hp ∷ ps) (q , []) hip abs 
    = nat-≤-abs (≤-trans hip (nat-≤-unstep abs)) refl
  bias-antisym (p , hp ∷ ps) (q , hq ∷ qs) (i1 x) (i1 y) 
    = nat-≤-abs (≤-trans y (nat-≤-unstep x)) refl
  bias-antisym (p , hp ∷ ps) (q , hq ∷ qs) (i2 (c≡ , rec)) (i1 x) 
    = nat-≤-abs x (sym c≡)
  bias-antisym (p , hp ∷ ps) (q , hq ∷ qs) (i1 x) (i2 (c≡ , rec)) 
    = nat-≤-abs x (sym c≡)
  bias-antisym (p , hp ∷ ps) (q , hq ∷ qs) (i2 (_ , r1)) (i2 (_ , r2)) 
    = bias-antisym (hp , ps) (hq , qs) r1 r2

  {-
  postulate
    bias-comm : {n : ℕ}{t : Tel n}{ty : U (suc n)}
              → (a b :  Dμ ⊥ₚ t ty)
              → (as bs : Patchμ t ty)
              → bias (a ∷ as) (b ∷ bs) ≡ not (bias (b ∷ bs) (a ∷ as))
  
  bias-comm (Dμ-A ()) _ _ _
  bias-comm _ (Dμ-A ()) _ _
  bias-comm (Dμ-del x) (Dμ-dwn x₁) da db = refl
  bias-comm (Dμ-dwn x) (Dμ-ins x₁) da db = refl
  bias-comm (Dμ-dwn x) (Dμ-del x₁) da db = refl
  bias-comm (Dμ-ins x) (Dμ-dwn x₁) da db = refl
  bias-comm (Dμ-ins x) (Dμ-ins x₁) [] [] = {!!}
  bias-comm (Dμ-ins x) (Dμ-ins x₁) [] (x₂ ∷ db) = {!!}
  bias-comm (Dμ-ins x) (Dμ-ins x₁) (x₂ ∷ da) [] = {!!}
  bias-comm (Dμ-ins x) (Dμ-ins x₁) (x₂ ∷ da) (x₃ ∷ db) = {!!}
  bias-comm (Dμ-ins x) (Dμ-del x₁) da db = {!!}
  bias-comm (Dμ-del x) (Dμ-ins x₁) da db = {!!}
  bias-comm (Dμ-del x) (Dμ-del x₁) da db = {!!}
  bias-comm (Dμ-dwn x) (Dμ-dwn x₁) da db = {!!}
  -}
\end{code}

%<*lubmu-def>
\begin{code}
  _⊔μ_ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
      → Patchμ t ty → Patchμ t ty → Patchμ t ty
  _⊔μ_ [] db = db
  _⊔μ_ da [] = da
  _⊔μ_ {ty = ty} (a ∷ da) (b ∷ db) with comp (costL (a ∷ da)) (costL (b ∷ db))
  ...| LE _ = a ∷ da
  ...| GE _ = b ∷ db
  ...| EQ p with bias-dec (a , da) (b , db)
  ...| yes _ = a ∷ da
  ...| no _  = b ∷ db
\end{code}
%</lubmu-def>

\begin{code}
  ⊔μ-elim : {n : ℕ}{t : Tel n}{ty : U (suc n)}{P : Patchμ t ty → Set}
          → (da db : Patchμ t ty)
          → P da → P db → P (da ⊔μ db)
  ⊔μ-elim [] db pda pdb = pdb
  ⊔μ-elim (a ∷ da) [] pda pdb = pda
  ⊔μ-elim (a ∷ da) (b ∷ db) pda pdb 
    with comp (costL (a ∷ da)) (costL (b ∷ db))
  ...| LE p = pda
  ...| GE p = pdb
  ...| EQ p with bias-dec (a , da) (b , db)
  ...| yes _ = pda
  ...| no _  = pdb
\end{code}

begin{code}
  ⊔μ-comm : {n : ℕ}{t : Tel n}{ty : U (suc n)}
          → (da db : Patchμ t ty)
          → da ⊔μ db ≡ db ⊔μ da
  ⊔μ-comm [] [] = refl
  ⊔μ-comm [] (x ∷ db) = refl
  ⊔μ-comm (x ∷ da) [] = refl
  ⊔μ-comm (a ∷ da) (b ∷ db) with comp (costL (a ∷ da)) (costL (b ∷ db)) 
  ...| LE x rewrite comp-GE x = refl
  ...| GE x rewrite comp-LE x = refl
  ...| EQ x rewrite comp-EQ (sym x)
               with bias-dec (a , da) (b , db) 
                  | bias-dec (b , db) (a , da)
  ...| yes as | yes bs = ⊥-elim (bias-antisym (a , da) (b , db) as bs)
  ...| no  as | no  bs = ⊥-elim (bs {!!})
  ...| yes _  | no  _  = refl
  ...| no  _  | yes _  = refl
          

  postulate
    ⊔μ-assoc : {n : ℕ}{t : Tel n}{ty : U (suc n)}
             → (da db dc : Patchμ t ty)
             → da ⊔μ (db ⊔μ dc) ≡ (da ⊔μ db) ⊔μ dc
end{code}
  ⊔μ-assoc da db dc 
    with comp (costL da) (costL db)
       | comp (costL db) (costL dc)
  ...| LE p | LE q
     rewrite comp-LE (≤-trans p (nat-≤-unstep q)) 
           | nat-≤-strict {m = costL db} {p = nat-≤-abs p} p 
           | nat-≤-dec p
           = refl
  ...| LE p | GE q = {!!}
  ...| LE p | EQ q = {!!}
  ...| GE p | LE q = {!!}
  ...| GE p | GE q = {!!}
  ...| GE p | EQ q = {!!}
  ...| EQ p | LE q = {!!}
  ...| EQ p | GE q = {!!}
  ...| EQ p | EQ q = {!!}
\end{code}
