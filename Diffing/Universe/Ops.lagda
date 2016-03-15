\begin{code}
open import Prelude

open import Diffing.Universe.Syntax
open import Diffing.Utils.Vector

open import Relation.Binary.PropositionalEquality
open import Data.List.Properties
    using (length-map; length-++; map-compose)

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
  children-lvl i unit          = []
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
  substituting them for unit.

%<*value>
\begin{code}
  forget : {n : ℕ}{a : U n}{t : Tel n}
         → (i : Fin n)
         → ElU a t
         → ElU a (tel-forget i t)
  forget i unit = unit
  forget i (inl el) = inl (forget i el)
  forget i (inr el) = inr (forget i el)
  forget i (ela , elb) = forget i ela , forget i elb
  forget fz (top el) = top unit
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
  arity-lvl i unit = 0
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
  ch-ar-lemma-lvl i unit = refl
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
  forget-arity-lemma i unit = refl
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
  plug-lvl {a = u1} i unit v = unit
  plug-lvl {a = a ⊕ b} i (inl el) v = inl (plug-lvl i el v)
  plug-lvl {a = a ⊕ b} i (inr el) v = inr (plug-lvl i el v)
  plug-lvl {a = a ⊗ b} i (ela , elb) v 
    = let va , vb = vsplit (arity-lvl i ela) v
      in plug-lvl i ela va
       , plug-lvl i elb vb
  plug-lvl {a = def F x} i (red el) v 
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
  plug-lvl-correct i unit 
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

