\begin{code}
open import Prelude

open import Diffing.Universe.Syntax
open import Diffing.Utils.Vector

open import Relation.Binary.PropositionalEquality
open import Data.List.Properties
    using (length-map; length-++; map-compose)
open import Data.Nat.Properties.Simple
    using (+-comm; +-assoc)

module Diffing.Universe.Ops where
\end{code}


Now we can start defining a few generic operations on terms.

  (children-lvl i) takes an element and returns a list of 
  terms corresponding to variables indexed by i.
%<*children-lvl>
\begin{code}
  children-lvl : {n : ℕ}{t : Tel n}{a : U n} 
               → (i : Fin n) → ElU a t 
               → List (ElU (tel-lkup i t) t)
  children-lvl i void          = []
  children-lvl i (inl el)      = children-lvl i el
  children-lvl i (inr el)      = children-lvl i el
  children-lvl i (ela , elb)   = children-lvl i ela ++ children-lvl i elb
  children-lvl fz (top el)     = pop el ∷ []
  children-lvl (fs i) (top el) = map pop (children-lvl i el)
  children-lvl fz (pop _)      = []
  children-lvl (fs i) (pop el) = map pop (children-lvl i el)
  children-lvl i (mu el)       = map unpop (children-lvl (fs i) el)
  children-lvl i (red el)      = map unpop (children-lvl (fs i) el)
\end{code}
%</children-lvl>

\begin{code}
  childrenℕ : {n : ℕ}{t : Tel n}{a : U n} 
            → (i : ℕ) → ElU a t 
            → List (ElU (tel-lkup-ℕ i t) t)
  childrenℕ i void = []
  childrenℕ i (inl el) = childrenℕ i el
  childrenℕ i (inr el) = childrenℕ i el
  childrenℕ i (ela , elb) = childrenℕ i ela ++ childrenℕ i elb
  childrenℕ zero (top el) = pop el ∷ []
  childrenℕ (suc i) (top el) = map pop (childrenℕ i el)
  childrenℕ zero (pop el) = []
  childrenℕ (suc i) (pop el) = map pop (childrenℕ i el)
  childrenℕ i (mu el) = map unpop (childrenℕ (suc i) el)
  childrenℕ i (red el) = map unpop (childrenℕ (suc i) el)
\end{code}

  A mmore usefull variant returning the immediate children.

%<*children-type>
\begin{code}
  children : {n : ℕ}{t : Tel n}{a : U (suc n)}{b : U n}
           → ElU a (tcons b t) → List (ElU b t)
\end{code}
%</children-type>
\begin{code}
  children el = map unpop (children-lvl fz el)
\end{code}

  (forget i) takes a term and ignores the terms at level i,
  substituting them for void.

%<*value>
\begin{code}
  forget : {n : ℕ}{a : U n}{t : Tel n}
         → (i : Fin n)
         → ElU a t
         → ElU a (tel-forget i t)
  forget i void = void
  forget i (inl el) = inl (forget i el)
  forget i (inr el) = inr (forget i el)
  forget i (ela , elb) = forget i ela , forget i elb
  forget fz (top el) = top void
  forget (fs i) (top el) = top (forget i el)
  forget fz (pop el) = pop el
  forget (fs i) (pop el) = pop (forget i el)
  forget i (mu el) = mu (forget (fs i) el)
  forget i (red el) = red (forget (fs i) el)
\end{code}
%</value>

  Arity counts the number of variables indexed by i.

%<*arity-lvl>
\begin{code}
  arity-lvl : {n : ℕ}{t : Tel n}{a : U n}
            → Fin n → ElU a t → ℕ
  arity-lvl i void = 0
  arity-lvl i (inl el) = arity-lvl i el
  arity-lvl i (inr el) = arity-lvl i el
  arity-lvl i (ela , elb) = arity-lvl i ela + arity-lvl i elb
  arity-lvl fz (top el) = 1
  arity-lvl (fs i) (top el) = arity-lvl i el
  arity-lvl fz (pop el) = 0
  arity-lvl (fs i) (pop el) = arity-lvl i el
  arity-lvl i (mu el) = arity-lvl (fs i) el
  arity-lvl i (red el) = arity-lvl (fs i) el  
\end{code}
%</arity-lvl>

  Again, a more useful variant.

%<*arity-type>
\begin{code}
  arity : {n : ℕ}{t : Tel n}{a : U (suc n)}{b : U n}
        → ElU a (tcons b t) → ℕ
\end{code}
%</arity-type>
\begin{code}
  arity el = arity-lvl fz el
\end{code}

  Now, a few lemmas come in handy.
  Arity and children are consistent:

\begin{code}
  ch-ar-lemma-lvl : {n : ℕ}{t : Tel n}{a : U n}
          → (i : Fin n)(x : ElU a t)
          → length (children-lvl i x) ≡ arity-lvl i x
  ch-ar-lemma-lvl i void = refl
  ch-ar-lemma-lvl i (inl x) = ch-ar-lemma-lvl i x
  ch-ar-lemma-lvl i (inr x) = ch-ar-lemma-lvl i x
  ch-ar-lemma-lvl i (xa , xb) = trans (length-++ (children-lvl i xa)) 
                          (cong₂ _+_ (ch-ar-lemma-lvl i xa) (ch-ar-lemma-lvl i xb))
  ch-ar-lemma-lvl fz (top x)     = refl
  ch-ar-lemma-lvl (fs i) (top x) 
    = trans (length-map pop (children-lvl i x)) 
            (ch-ar-lemma-lvl i x)
  ch-ar-lemma-lvl fz (pop x)     = refl
  ch-ar-lemma-lvl (fs i) (pop x) 
    = trans (length-map pop (children-lvl i x)) 
            (ch-ar-lemma-lvl i x)
  ch-ar-lemma-lvl i (mu x) 
    = trans (length-map unpop (children-lvl (fs i) x)) 
            (ch-ar-lemma-lvl (fs i) x)
  ch-ar-lemma-lvl i (red x) 
    = trans (length-map unpop (children-lvl (fs i) x)) 
            (ch-ar-lemma-lvl (fs i) x)
\end{code}

%<*children-arity-lemma-type>
\begin{code}
  children-arity-lemma
    : {n : ℕ}{t : Tel n}{a : U (suc n)}{b : U n}
    → (x : ElU a (tcons b t))
    → length (children x) ≡ arity x
\end{code}
%</children-arity-lemma-type>
\begin{code}
  children-arity-lemma el
    rewrite (length-map unpop (children-lvl fz el))
         = ch-ar-lemma-lvl fz el
\end{code}

  And forgeting values doesnt change arity, for it doesn't
  change the actual top-level type.

%<*forget-arity-lemma-type>
\begin{code}
  forget-arity-lemma
    : {n : ℕ}{t : Tel n}{a : U n}
    → (i : Fin n)
    → (el : ElU a t)
    → arity-lvl i el ≡ arity-lvl i (forget i el)
\end{code}
%</forget-arity-lemma-type>
\begin{code}
  forget-arity-lemma i void = refl
  forget-arity-lemma i (inl el) = forget-arity-lemma i el
  forget-arity-lemma i (inr el) = forget-arity-lemma i el
  forget-arity-lemma i (ela , elb) 
    = cong₂ _+_ (forget-arity-lemma i ela) (forget-arity-lemma i elb)
  forget-arity-lemma fz (top el) = refl
  forget-arity-lemma (fs i) (top el) = forget-arity-lemma i el
  forget-arity-lemma fz (pop el) = refl
  forget-arity-lemma (fs i) (pop el) = forget-arity-lemma i el
  forget-arity-lemma i (mu el) = forget-arity-lemma (fs i) el
  forget-arity-lemma i (red el) = forget-arity-lemma (fs i) el
\end{code}

  Now, the most interesting plug and unplug operations.
  We can always represent an element as a rosetree with the correct
  arity!

  On a lvl-polymorphic view first,

\begin{code}
  unplug-lvl : {n : ℕ}{t : Tel n}{a : U n}
             → (i : Fin n)
             → (el : ElU a t)
             → Σ (ElU a (tel-forget i t)) 
                 (λ x → Vec (ElU (tel-lkup i t) t) (arity-lvl i x))
  unplug-lvl {t = t} i el 
    = forget i el 
    , vec (children-lvl i el) 
          (trans (ch-ar-lemma-lvl i el) (forget-arity-lemma i el))
\end{code}

  Following with the more useful top-level unplugging.

%<*unplug-type>
\begin{code}
  unplug : {n : ℕ}{t : Tel n}{a : U (suc n)}{b : U n}
         → (el : ElU a (tcons b t))
         → Σ (ElU a (tcons u1 t)) (λ x → Vec (ElU b t) (arity x))
\end{code}
%</unplug-type>
\begin{code}
  unplug el with unplug-lvl fz el
  ...| hd , ch = hd , vmap unpop ch
\end{code}

\begin{code}
  term-hd : {n : ℕ}{t : Tel n}{a : U (suc n)}{b : U n}
          → (el : ElU a (tcons b t))
          → (ElU a (tcons u1 t))
  term-hd = p1 ∘ unplug
\end{code}

  Plug follows the same approach,

\begin{code}
  plug-lvl : {n : ℕ}{t : Tel n}{a : U n}
      → (i : Fin n)
      → (el : ElU a (tel-forget i t))
      → Vec (ElU (tel-lkup i t) t) (arity-lvl i el)
      → ElU a t
  plug-lvl {a = u0} i () v
  plug-lvl {a = u1} i void v = void
  plug-lvl {a = a ⊕ b} i (inl el) v = inl (plug-lvl i el v)
  plug-lvl {a = a ⊕ b} i (inr el) v = inr (plug-lvl i el v)
  plug-lvl {a = a ⊗ b} i (ela , elb) v 
    = let va , vb = vsplit (arity-lvl i ela) v
      in plug-lvl i ela va
       , plug-lvl i elb vb
  plug-lvl {a = β F x} i (red el) v 
     = red (plug-lvl (fs i) el (vmap pop v))
  plug-lvl {a = μ a} i (mu el) v 
    = mu (plug-lvl (fs i) el (vmap pop v))
  plug-lvl {t = tcons x t} {vl} fz (top el) (pop k ∷ []) 
    = top k
  plug-lvl {t = tcons x t} {vl} (fs i) (top el) v 
    = top (plug-lvl i el (vmap unpop v))
  plug-lvl {t = tcons x t} {wk a} fz (pop el) v 
    = pop el
  plug-lvl {t = tcons x t} {wk a} (fs i) (pop el) v 
    = pop (plug-lvl i el (vmap unpop v))
\end{code}

%<*plug-type>
\begin{code}
  plug : {n : ℕ}{t : Tel n}{a : U (suc n)}{b : U n}
       → (el : ElU a (tcons u1 t))
       → Vec (ElU b t) (arity el)
       → ElU a (tcons b t)
\end{code}
%</plug-type>
\begin{code}
  plug el v = plug-lvl fz el (vmap pop v)
\end{code}

  And finally, correctness of plug.

\begin{code}
  aux-lemma-1 : {n : ℕ}{A B : Set}{t : Tel n}{a : U n}
              → (i : Fin n)(el : ElU a t)
              → {f : ElU (tel-lkup i t) t → A}{g : A → B}
              → length (map g (map f (children-lvl i el)))
              ≡ arity-lvl i (forget i el)
  aux-lemma-1 i el {f = f} {g = g}
    = trans (length-map g (map f (children-lvl i el))) 
      (trans (length-map f (children-lvl i el)) 
       (trans (ch-ar-lemma-lvl i el) 
        (forget-arity-lemma i el)))

  map-lemma : {A B : Set}{f : A → B}{g : B → A}
            → (l : List A)
            → (∀ x → g (f x) ≡ x)
            → map g (map f l) ≡ l
  map-lemma [] prf      = refl
  map-lemma (x ∷ l) prf = cong₂ _∷_ (prf x) (map-lemma l prf)

  vmap-lemma
    : {k : ℕ}{A B : Set}{f : A → B}{g : B → A}
    → (v : Vec A k)
    → (∀ x → g (f x) ≡ x)
    → vmap g (vmap f v) ≡ v
  vmap-lemma [] prf      = refl
  vmap-lemma (x ∷ k) prf = cong₂ _∷_ (prf x) (vmap-lemma k prf)

  unpop-top
    : {n : ℕ}{t : Tel n}{a : U n}
    → (i : Fin n)
    → (el : ElU a t)
    → vmap unpop (p2 (unplug-lvl (fs i) (top el)))
    ≡ p2 (unplug-lvl i el)
  unpop-top i el with unplug-lvl i el
  ...| hd , ch 
     = trans (vmap-vec unpop (map pop (children-lvl i el)) 
               {q = aux-lemma-1 i el} ) 
             (vec-≡ (map-lemma (children-lvl i el) 
                    (λ x → refl)))

  unpop-pop
    : {n : ℕ}{t : Tel n}{a b : U n}
    → (i : Fin n)
    → (el : ElU a t)
    → vmap (unpop {x = b}) (p2 (unplug-lvl (fs i) (pop el)))
    ≡ p2 (unplug-lvl i el)
  unpop-pop i el with unplug-lvl i el
  ...| hd , ch 
     = trans (vmap-vec unpop (map pop (children-lvl i el)) 
               {q = aux-lemma-1 i el} ) 
             (vec-≡ (map-lemma (children-lvl i el) 
                    (λ x → refl)))

  pop-mu
    : {n : ℕ}{t : Tel n}{a : U (suc n)}
    → (i : Fin n)
    → (el : ElU a (tcons (μ a) t))
    → vmap pop (p2 (unplug-lvl i (mu el)))
    ≡ p2 (unplug-lvl (fs i) el)
  pop-mu i el with unplug-lvl (fs i) el
  ...| hd , ch 
     = trans (vmap-vec pop (map unpop (children-lvl (fs i) el))
               {q = aux-lemma-1 (fs i) el}) 
             (vec-≡ (map-lemma (children-lvl (fs i) el) 
                    (λ { (pop x) → refl })))

  pop-red
    : {n : ℕ}{t : Tel n}{a : U (suc n)}{b : U n}
    → (i : Fin n)
    → (el : ElU a (tcons b t))
    → vmap pop (p2 (unplug-lvl i (red el)))
    ≡ p2 (unplug-lvl (fs i) el)
  pop-red i el with unplug-lvl (fs i) el
  ...| hd , ch 
     = trans (vmap-vec pop (map unpop (children-lvl (fs i) el))
               {q = aux-lemma-1 (fs i) el}) 
             (vec-≡ (map-lemma (children-lvl (fs i) el) 
                    (λ { (pop x) → refl })))
      

  plug-lvl-correct
    : {n : ℕ}{t : Tel n}{a : U n}
    → (i : Fin n)
    → (el : ElU a t)
    → el ≡ plug-lvl i (p1 (unplug-lvl i el)) (p2 (unplug-lvl i el))
  plug-lvl-correct i void 
    = refl
  plug-lvl-correct i (inl el) 
    = cong inl (plug-lvl-correct i el)
  plug-lvl-correct i (inr el) 
    = cong inr (plug-lvl-correct i el)
  plug-lvl-correct fz (top el) = refl
  plug-lvl-correct (fs i) (top el) 
    = cong top 
      (subst (λ P → el ≡ plug-lvl i (forget i el) P) 
      (sym (unpop-top i el)) (plug-lvl-correct i el))
  plug-lvl-correct fz (pop el) = refl
  plug-lvl-correct (fs i) (pop el) 
    = cong pop 
      (subst (λ P → el ≡ plug-lvl i (forget i el) P) 
      (sym (unpop-pop i el)) (plug-lvl-correct i el))
  plug-lvl-correct i (mu el) 
    = cong mu 
      (subst (λ P → el ≡ plug-lvl (fs i) (forget (fs i) el) P) 
      (sym (pop-mu i el)) (plug-lvl-correct (fs i) el))
  plug-lvl-correct i (red el) 
    = cong red
      (subst (λ P → el ≡ plug-lvl (fs i) (forget (fs i) el) P) 
      (sym (pop-red i el)) (plug-lvl-correct (fs i) el))
  plug-lvl-correct i (ela , elb) 
    = cong₂ _,_ (sym (prod1 i ela elb)) (sym (prod2 i ela elb))
    where
      prod1 : {n : ℕ}{t : Tel n}{a b : U n}
            → (i : Fin n)(ela : ElU a t)(elb : ElU b t)
            → plug-lvl i (forget i ela) (p1
               (vsplit (arity-lvl i (forget i ela))
                 (p2 (unplug-lvl i (ela , elb))))
             ) ≡ ela
      prod1 i ela elb with unplug-lvl i (ela , elb)
      ...| (hdA , hdB) , ch 
         = subst (λ P → plug-lvl i (forget i ela) P ≡ ela) 
           (sym (trans 
                (vsplit-elim-1 (children-lvl i ela) (children-lvl i elb)) 
                refl)) 
           (sym (plug-lvl-correct i ela))

      prod2 : {n : ℕ}{t : Tel n}{a b : U n}
            → (i : Fin n)(ela : ElU a t)(elb : ElU b t)
            → plug-lvl i (forget i elb) (p2
               (vsplit (arity-lvl i (forget i ela))
                 (p2 (unplug-lvl i (ela , elb))))
             ) ≡ elb
      prod2 i ela elb with unplug-lvl i (ela , elb)
      ...| (hdA , hdB) , ch 
         = subst (λ P → plug-lvl i (forget i elb) P ≡ elb) 
           (sym (trans 
                (vsplit-elim-2 
                  {m = arity-lvl i (forget i ela)} 
                  (children-lvl i ela) 
                  (children-lvl i elb)) 
                refl)) 
           (sym (plug-lvl-correct i elb))
\end{code}


%<*plug-correct-type>
\begin{code}
  plug-correct : {n : ℕ}{t : Tel n}{a : U (suc n)}{b : U n}
               → (el : ElU a (tcons b t))
               → el ≡ plug (p1 (unplug el)) (p2 (unplug el))
\end{code}
%</plug-correct-type>
\begin{code}
  plug-correct {a = a} el with unplug el
  ...| hd , ch  
     = subst (λ P → el ≡ plug-lvl fz (forget fz el) P) 
             (sym (vmap-lemma 
                    (vec (children-lvl fz el) _) 
                    (λ { (pop x) → refl }))) 
             (plug-lvl-correct fz el)
\end{code}

  Arity and plugging lemmas

begin{code}
  ↑_ : {n : ℕ} → Fin n → Fin (suc n)
  ↑ fz = fz
  ↑ fs i = fs (↑ i)

  δ : {n : ℕ} → Fin n → Fin n → Fin n
  δ i fz = i
  δ fz (fs j) = fz
  δ (fs i) (fs j) = ↑ δ i j

  -- Sum of arities.
  Σ-ar-lvl : {n : ℕ}{t : Tel n}{a : U n}
           → Fin n → List (ElU a t) → ℕ
  Σ-ar-lvl i [] = 0
  Σ-ar-lvl i (x ∷ xs) = arity-lvl i x + Σ-ar-lvl i xs

  Σ-ar-unpop-lemma
    : {n : ℕ}{t : Tel n}{ty : U n}{a : U n}
    → (i : Fin n)(x : List (ElU (wk ty) (tcons a t)))
    → Σ-ar-lvl (fs i) x ≡ Σ-ar-lvl i (map unpop x)
  Σ-ar-unpop-lemma i [] = refl
  Σ-ar-unpop-lemma i (pop x ∷ xs) 
    = {!!} -- cong (λ P → arity-lvl i x + P) (Σ-ar-unpop-lemma i xs)

  Σ-ar-pop-lemma
    : {n : ℕ}{t : Tel n}{ty : U n}{a : U n}
    → (i : Fin n)(x : List (ElU ty t))
    → Σ-ar-lvl (fs i) (map (pop {a = a}) x) ≡ Σ-ar-lvl i x
  Σ-ar-pop-lemma i [] = refl
  Σ-ar-pop-lemma {a = a} i (x ∷ xs) 
    = {!!} -- cong (λ P → arity-lvl i x + P) (Σ-ar-pop-lemma {a = a} i xs)

  Σ-ar-++-commute
    : {n : ℕ}{t : Tel n}{ty : U n}
    → (i : Fin n)(xs ys : List (ElU ty t))
    → Σ-ar-lvl i (xs ++ ys) ≡ Σ-ar-lvl i xs + Σ-ar-lvl i ys
  Σ-ar-++-commute i [] ys = refl
  Σ-ar-++-commute i (x ∷ xs) ys 
    = trans (cong (λ P → arity-lvl i x + P) (Σ-ar-++-commute i xs ys))
            (sym (+-assoc (arity-lvl i x) (Σ-ar-lvl i xs) (Σ-ar-lvl i ys)))

  +-exch : (m n o p : ℕ)
         → (m + n) + (o + p) ≡ (m + o) + (n + p)
  +-exch m n o p = 
    trans (sym (+-assoc (m + n) o p)) (
      trans (cong (λ P → P + p) (+-assoc m n o)) (
        trans (cong (λ P → m + P + p) (+-comm n o)) (
          trans (cong (λ P → P + p) (sym (+-assoc m o n)))
                (+-assoc (m + o) n p)
          )))

  data _≤-Fin_ : {n : ℕ} → Fin n → Fin n → Set where
    base : ∀{n}{i : Fin (suc n)} → _≤-Fin_ {suc n} fz i
    step : ∀{n}{i j : Fin n}
         → i ≤-Fin j → fs i ≤-Fin fs j

  δ-fs-lemma : {n : ℕ}(i : Fin n)(j : Fin (suc n))
             → (j ≤-Fin (↑ i)) → ∃ (λ x → δ (fs i) j ≡ fs x)
  δ-fs-lemma i fz hip = i , refl
  δ-fs-lemma fz (fs j) ()
  δ-fs-lemma (fs i) (fs j) (step hip) 
    with δ-fs-lemma i j hip
  ...| x' , prf rewrite prf = (↑ x') , refl

  arity-split-lemma 
    : {n : ℕ}{t : Tel n}{ty : U (suc n)}{a : U n}
    → (i j : Fin n)(hip : j ≤-Fin i)(x : ElU ty (tcons a t))
    → arity-lvl (fs i) x 
    ≡ arity-lvl (fs i) (forget (↑ j) x) + Σ-ar-lvl (δ i j) (children-lvl j {!x!})
  arity-split-lemma i j hip void = refl
  arity-split-lemma i j hip (inl x) = arity-split-lemma i j hip x
  arity-split-lemma i j hip (inr x) = arity-split-lemma i j hip x
  arity-split-lemma i j hip (x , y) 
    = {!!}
  {-
    rewrite Σ-ar-++-commute (δ i j) (children-lvl j x) (children-lvl j y)
          | +-exch (arity-lvl (fs i) (forget j x)) (arity-lvl (fs i) (forget j y))
                   (Σ-ar-lvl (δ i j) (children-lvl j x)) (Σ-ar-lvl (δ i j) (children-lvl j y))
          = cong₂ _+_ (arity-split-lemma i j hip x)
                      (arity-split-lemma i j hip y)
  -}
  arity-split-lemma i fz hip (top x) = sym (+-comm (arity-lvl i x) zero)
  arity-split-lemma fz (fs j) () (top x)
  arity-split-lemma {t = tcons t ts} (fs i) (fs j) (step hip) (top x) 
    = {!!} -- trans (arity-split-lemma i j hip x) 
        --    (cong (λ P → arity-lvl (fs i) (forget j x) + P) (sym (Σ-ar-pop-lemma (δ i j) (children-lvl j x))))
  arity-split-lemma i fz hip (pop x) = sym (+-comm (arity-lvl i x) zero)
  arity-split-lemma fz (fs j) () (pop x)
  arity-split-lemma {t = tcons t ts} (fs i) (fs j) (step hip) (pop x)
    = {!!} -- trans (arity-split-lemma i j hip x) 
            -- (cong (λ P → arity-lvl (fs i) (forget j x) + P) (sym (Σ-ar-pop-lemma (δ i j) (children-lvl j x))))
  arity-split-lemma i j hip (mu x) 
    = trans (arity-split-lemma (fs i) (fs j) (step hip) x) 
             {!!} -- (cong (λ P → arity-lvl (fs (fs i)) (forget (fs j) x) + P) 
             --     (Σ-ar-unpop-lemma (δ i j) (children-lvl (fs j) x)))
  arity-split-lemma i j hip (red x) 
    = trans (arity-split-lemma (fs i) (fs j) (step hip) x) 
            {!!} -- (cong (λ P → arity-lvl (fs (fs i)) (forget (fs j) x) + P) 
                 -- (Σ-ar-unpop-lemma (δ i j) (children-lvl (fs j) x)))

  arity-split-lemma-fz
    : {n : ℕ}{t : Tel n}{ty : U (suc n)}{a : U n}
    → (i : Fin n)(x : ElU ty (tcons a t))
    → arity-lvl (fs i) x 
    ≡ arity-lvl (fs i) (term-hd x) + Σ-ar-lvl i (children x)
  arity-split-lemma-fz {n} {t} {ty} {a} i x 
    = {!δ i fz!}

end{code}
