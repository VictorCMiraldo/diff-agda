\begin{code}
open import Prelude

open import Data.List.Properties
    using (length-map)

open import Diffing.Universe.Syntax
open import Diffing.Universe.Operations
open import Diffing.Universe.Operations.Properties
open import Diffing.Universe.Plugging
open import Diffing.Utils.Vector

module Diffing.Universe.Plugging.Properties where
\end{code}

  Here we prove that "plug ∘ unplug ≡ id". 
  Although they actually make an isomoprhism, we don't need
  the proof for "unplug ∘ plug ≡ id" anywhere, therefore
  we ommit it.

  There are a bunch of auxiliary lemmas that must be proved
  before hand, however.

\begin{code}
  private
    aux-lemma : {n : ℕ}{A B : Set}{t : T n}{a : U n}
                → (i : ℕ)(el : ElU a t)
                → {f : ElU (tel-lkup i t) t → A}{g : A → B}
                → length (map g (map f (ch i el))) ≡ ar i (fgt i el)
    aux-lemma i el {f = f} {g = g}
      = trans (length-map g (map f (ch i el))) 
        (trans (length-map f (ch i el)) 
         (trans (ch-ar-lemma i el) 
          (fgt-ar-lemma i el)))

    map-lemma : {A B : Set}{f : A → B}{g : B → A}
              → (l : List A)
              → (∀ x → g (f x) ≡ x)
              → map g (map f l) ≡ l
    map-lemma [] prf      = refl
    map-lemma (x ∷ l) prf = cong₂ _∷_ (prf x) (map-lemma l prf)

    unpop-top
      : {n : ℕ}{t : T n}{a : U n}
      → (i : ℕ)
      → (el : ElU a t)
      → vmap unpop (p2 (unplug (suc i) (top el)))
      ≡ p2 (unplug i el)
    unpop-top i el 
      = trans (vmap-vec unpop (map pop (ch i el)) 
                 {q = aux-lemma i el} ) 
              (vec-≡ (map-lemma (ch i el) 
                     (λ x → refl)))

    unpop-pop
      : {n : ℕ}{t : T n}{a b : U n}
      → (i : ℕ)
      → (el : ElU a t)
      → vmap (unpop {x = b}) (p2 (unplug (suc i) (pop el)))
      ≡ p2 (unplug i el)
    unpop-pop i el
      = trans (vmap-vec unpop (map pop (ch i el)) 
                 {q = aux-lemma i el} ) 
              (vec-≡ (map-lemma (ch i el) 
                     (λ x → refl)))

    pop-mu
      : {n : ℕ}{t : T n}{a : U (suc n)}
      → (i : ℕ)
      → (el : ElU a (μ a ∷ t))
      → vmap pop (p2 (unplug i (mu el)))
      ≡ p2 (unplug (suc i) el)
    pop-mu i el 
      = trans (vmap-vec pop (map unpop (ch (suc i) el))
                 {q = aux-lemma (suc i) el}) 
              (vec-≡ (map-lemma (ch (suc i) el) 
                     (λ { (pop x) → refl })))

    pop-red
      : {n : ℕ}{t : T n}{a : U (suc n)}{b : U n}
      → (i : ℕ)
      → (el : ElU a (b ∷ t))
      → vmap pop (p2 (unplug i (red el)))
      ≡ p2 (unplug (suc i) el)
    pop-red i el 
      = trans (vmap-vec pop (map unpop (ch (suc i) el))
                 {q = aux-lemma (suc i) el}) 
              (vec-≡ (map-lemma (ch (suc i) el) 
                     (λ { (pop x) → refl })))
\end{code}

%<*plug-correct-type>
\begin{code}
  plug-correct
    : {n : ℕ}{t : T n}{ty : U n}
    → (i : ℕ)(el : ElU ty t)
    → el ≡ plug i (p1 (unplug i el)) (p2 (unplug i el))
\end{code}
%</plug-correct-type>
\begin{code}
  plug-correct i unit 
    = refl
  plug-correct i (inl el) 
    = cong inl (plug-correct i el)
  plug-correct i (inr el) 
    = cong inr (plug-correct i el)
  plug-correct zero (top el) 
    = refl
  plug-correct (suc i) (top el) 
    = cong top 
      (subst (λ P → el ≡ plug i (fgt i el) P) 
      (sym (unpop-top i el)) (plug-correct i el))
  plug-correct zero (pop el) 
    = refl
  plug-correct (suc i) (pop el) 
    = cong pop 
      (subst (λ P → el ≡ plug i (fgt i el) P) 
      (sym (unpop-pop i el)) (plug-correct i el))
  plug-correct i (mu el) 
    = cong mu 
      (subst (λ P → el ≡ plug (suc i) (fgt (suc i) el) P) 
      (sym (pop-mu i el)) (plug-correct (suc i) el))
  plug-correct i (red el) 
    = cong red
      (subst (λ P → el ≡ plug (suc i) (fgt (suc i) el) P) 
      (sym (pop-red i el)) (plug-correct (suc i) el))
  plug-correct i (ela , elb) 
    = cong₂ _,_ (sym (prod1 i ela elb)) (sym (prod2 i ela elb))
    where
      prod1 : {n : ℕ}{t : T n}{a b : U n}
            → (i : ℕ)(ela : ElU a t)(elb : ElU b t)
            → plug i (fgt i ela) (p1
               (vsplit (ar i (fgt i ela))
                 (p2 (unplug i (ela , elb))))
             ) ≡ ela
      prod1 i ela elb with unplug i (ela , elb)
      ...| (hdA , hdB) , CH 
         = subst (λ P → plug i (fgt i ela) P ≡ ela) 
           (sym (trans 
                (vsplit-elim-1 (ch i ela) (ch i elb)) 
                refl)) 
           (sym (plug-correct i ela))

      prod2 : {n : ℕ}{t : T n}{a b : U n}
            → (i : ℕ)(ela : ElU a t)(elb : ElU b t)
            → plug i (fgt i elb) (p2
               (vsplit (ar i (fgt i ela))
                 (p2 (unplug i (ela , elb))))
             ) ≡ elb
      prod2 i ela elb with unplug i (ela , elb)
      ...| (hdA , hdB) , CH
         = subst (λ P → plug i (fgt i elb) P ≡ elb) 
           (sym (trans 
                (vsplit-elim-2 
                  {m = ar i (fgt i ela)} 
                  (ch i ela) 
                  (ch i elb)) 
                refl)) 
           (sym (plug-correct i elb))
\end{code}
