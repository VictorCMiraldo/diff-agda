\begin{code}
open import Prelude

open import Data.Nat
  using (_≤_; s≤s; z≤n)
open import Data.List.Properties
  using (length-map)

open import Diffing.Universe.Syntax
open import Diffing.Universe.Operations
open import Diffing.Universe.Operations.Properties
open import Diffing.Universe.Plugging
open import Diffing.Universe.Plugging.Properties
open import Diffing.Utils.Vector

module Diffing.Universe.Operations.Mu where
\end{code}

%<*mu-open>
\begin{code}
  μ-open : {n : ℕ}{t : T n}{ty : U (suc n)} 
         → ElU (μ ty) t → ElU ty (u1 ∷ t) × List (ElU (μ ty) t)
  μ-open (mu el) with unplug 0 el
  ...| HD , CH = HD , toList (vmap unpop CH)
\end{code}
%</mu-open>

%<*mu-hd-def>
\begin{code}
  μ-hd : {n : ℕ}{t : T n}{ty : U (suc n)} 
       → ElU (μ ty) t → ElU ty (u1 ∷ t)
  μ-hd = p1 ∘ μ-open
\end{code}
%</mu-hd-def>

%<*mu-ar-def>
\begin{code}
  μ-ar : {n : ℕ}{t : T n}{ty : U (suc n)} 
       → ElU (μ ty) t → ℕ
  μ-ar = ar 0 ∘ μ-hd
\end{code}
%</mu-ar-def>

%<*mu-ch-def>
\begin{code}
  μ-ch : {n : ℕ}{t : T n}{ty : U (suc n)} 
       → ElU (μ ty) t → List (ElU (μ ty) t)
  μ-ch = p2 ∘ μ-open
\end{code}
%</mu-ch-def>

%<*mu-ch-lemma>
\begin{code}
  μ-ch-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x : ElU ty (μ ty ∷ t))
             → μ-ch (mu x) ≡ map unpop (ch 0 x)
  μ-ch-lemma x with μ-open (mu x)
  ...| HD , CH 
     rewrite vmap-vec unpop (ch 0 x) 
             {trans (ch-ar-lemma 0 x) (fgt-ar-lemma 0 x)} 
             {trans (length-map unpop (ch 0 x)) 
                    (trans (ch-ar-lemma 0 x) (fgt-ar-lemma 0 x)) }
           = toList-vec (map unpop (ch zero x))
\end{code}
%</mu-ch-lemma>

%<*mu-open-ar-lemma>
\begin{code}
  μ-open-ar-lemma 
    : {n : ℕ}{t : T n}{ty : U (suc n)} 
    → (el : ElU (μ ty) t)
    → length (μ-ch el) ≡ μ-ar el
\end{code}
%</mu-open-ar-lemma>
\begin{code}
  μ-open-ar-lemma {n} {t} {ty} (mu el) 
     = length-toList (vmap unpop (vec (ch 0 el) _))
\end{code}


\begin{code}
  private
    list-split : {m : ℕ}{A : Set}(l : List A)
               → m ≤ length l
               → Σ (List A × List A) (λ ls → length (p1 ls) ≡ m)
    list-split [] z≤n = ([] , []) , refl
    list-split (x ∷ l) z≤n = ([] , x ∷ l) , refl
    list-split (x ∷ l) (s≤s p) with list-split l p
    ...| (la , lb) , prf = (x ∷ la , lb) , (cong suc prf)

    list-split-lemma 
      : {m : ℕ}{A : Set}(l1 l2 : List A){p : m ≤ length (l1 ++ l2)}
      → (q : length l1 ≡ m)
      → list-split (l1 ++ l2) p ≡ ((l1 , l2) , q)
    list-split-lemma [] [] {z≤n} refl = refl
    list-split-lemma [] (x ∷ l2) {z≤n} refl = refl
    list-split-lemma (x ∷ l1) l2 {s≤s p} refl
      with list-split-lemma l1 l2 {p} refl
    ...| hip rewrite hip = refl

    length-lemma 
      : {n : ℕ}{A : Set}(l1 l2 : List A)
      → length l1 ≡ n → n ≤ length (l1 ++ l2)
    length-lemma [] l2 refl = z≤n
    length-lemma (x ∷ l1) l2 refl = s≤s (length-lemma l1 l2 refl)
\end{code}

%<*mu-close>
\begin{code}
  μ-close : {n : ℕ}{t : T n}{ty : U (suc n)} 
          → ElU ty (u1 ∷ t) × List (ElU (μ ty) t) 
          → Maybe (ElU (μ ty) t × List (ElU (μ ty) t))
  μ-close (HD , CH) with ar 0 HD ≤?-ℕ length CH
  ...| no  _ = nothing
  ...| yes p with list-split CH p
  ...| (chA , rest) , prf 
     = just (mu (plug 0 HD (vmap pop (vec chA prf))) , rest)
\end{code}
%</mu-close>


%<*mu-close-correct-type>
\begin{code}
  μ-close-correct
    : {n : ℕ}{t : T n}{ty : U (suc n)}{a : ElU (μ ty) t}
      {hdA : ElU ty (u1 ∷ t)}{chA l : List (ElU (μ ty) t)}
    → μ-open a ≡ (hdA , chA)
    → μ-close (hdA , chA ++ l) ≡ just (a , l)
\end{code}
%</mu-close-correct-type>
\begin{code}
  μ-close-correct {a = mu a} {l = l} refl
    with ar 0 (μ-hd (mu a)) ≤?-ℕ length (μ-ch (mu a) ++ l)
  ...| no ¬q = ⊥-elim (¬q (length-lemma (μ-ch (mu a)) l (μ-open-ar-lemma (mu a))))
  ...| yes q 
    rewrite list-split-lemma 
       (toList (vmap unpop (vec (ch 0 a) 
               (trans (ch-ar-lemma 0 a) (fgt-ar-lemma 0 a))))) l
       {p = q}
       (length-toList (vmap unpop (vec (ch 0 a) 
               (trans (ch-ar-lemma 0 a) (fgt-ar-lemma 0 a)))))
     = cong (λ P → just (mu P , l)) 
       (subst (λ P → plug 0 (fgt 0 a) (vmap pop P) ≡ a) 
         (sym (vec-toList (vmap unpop (vec (ch 0 a)
              (trans (ch-ar-lemma 0 a) (fgt-ar-lemma 0 a)))))) 
         (subst (λ P → plug 0 (fgt 0 a) P ≡ a) 
           (sym (vmap-lemma (vec (ch 0 a)
                            (trans (ch-ar-lemma 0 a) (fgt-ar-lemma 0 a))) 
                            (λ { (pop x) → refl }))) 
           (sym (plug-correct 0 a))))
\end{code} 

%<*mu-ar-lemma>
\begin{code}
  μ-arity-lemma
    : {n : ℕ}{t : T n}{ty : U (suc n)}(x : ElU (μ ty) t)
    → (i : ℕ) 
    → ar i x ≡ ar (suc i) (μ-hd x) + ar* i (μ-ch x)
  μ-arity-lemma {n} {t} {ty} (mu x) i
    = trans (ar-lemma (suc i) 0 x) 
            (cong (λ P → ar (suc i) (fgt 0 x) + P) 
            (trans (sym (ar*-unpop i (ch 0 x))) 
                   (cong (λ P → ar* i P) (sym (μ-ch-lemma x)))))
\end{code}
%</mu-ar-lemma>


