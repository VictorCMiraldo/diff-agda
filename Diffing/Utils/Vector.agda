open import Prelude
open import Data.List.Properties
    using (length-map; length-++)
open import Data.Nat.Properties.Simple
     using (+-comm)

module Diffing.Utils.Vector where

  open import Data.Vec 
    using (Vec; []; _∷_; head; tail) 
    renaming (_++_ to _++v_)
    public

  suc-inj : ∀{m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  +-inj-1 : ∀{m n o} → m + n ≡ m + o → n ≡ o
  +-inj-1 {zero} p = p
  +-inj-1 {suc m} p = +-inj-1 {m = m} (suc-inj p)

  +-inj-2 : ∀{m n o} → n + m ≡ o + m → n ≡ o
  +-inj-2 {m} {n} {o} p 
    rewrite +-comm n m 
          | +-comm o m
          = +-inj-1 {m = m} p

  vec : {k : ℕ}{A : Set}(l : List A)
      → length l ≡ k → Vec A k
  vec []       refl = []
  vec {zero}  (x ∷ xs) ()
  vec {suc k} (x ∷ xs) p = x ∷ vec xs (suc-inj p)

  toList : {k : ℕ}{A : Set}(v : Vec A k)
         → List A
  toList []      = []
  toList (x ∷ v) = x ∷ toList v

  length-toList : {k : ℕ}{A : Set}(v : Vec A k)
                → length (toList v) ≡ k
  length-toList [] = refl
  length-toList (x ∷ v) = cong suc (length-toList v)

  vec-reduce : {k : ℕ}{A : Set}(l : List A){p q : length l ≡ k}
             → vec l p ≡ vec l q
  vec-reduce l {refl} {refl} = refl

  vec-toList : {k : ℕ}{A : Set}(v : Vec A k)
             → vec (toList v) (length-toList v) ≡ v
  vec-toList [] = refl
  vec-toList (x ∷ v) 
    = cong (_∷_ x) (trans (vec-reduce (toList v)) (vec-toList v))

  toList-vec : {k : ℕ}{A : Set}(l : List A){p : length l ≡ k}
             → toList (vec l p) ≡ l
  toList-vec [] {refl} = refl
  toList-vec (x ∷ l) {refl} = cong (_∷_ x) (toList-vec l)

  vec-≡ : {k : ℕ}{A : Set}{l₁ l₂ : List A}
          {p : length l₁ ≡ k}{q : length l₂ ≡ k}
        → l₁ ≡ l₂ → vec l₁ p ≡ vec l₂ q
  vec-≡ {l₁ = l} refl = vec-reduce l

  vmap : {k : ℕ}{A B : Set}(f : A → B)
       → Vec A k → Vec B k
  vmap f []       = []
  vmap f (x ∷ xs) = f x ∷ vmap f xs

  vmap-vec : {k : ℕ}{A B : Set}(f : A → B)(l : List A)
             {p : length l ≡ k}{q : length (map f l) ≡ k}
           → vmap f (vec l p) ≡ vec (map f l) q
  vmap-vec f []      {refl} {refl} = refl
  vmap-vec f (x ∷ l) {refl} {q}
    = cong (_∷_ (f x)) (trans (vmap-vec f l {q = suc-inj q}) 
                              (vec-reduce (map f l)))

  toList-vmap : {k : ℕ}{A B : Set}(f : A → B)(v : Vec A k)
              → toList (vmap f v) ≡ map f (toList v)
  toList-vmap f [] = refl
  toList-vmap f (x ∷ v) = cong (_∷_ (f x)) (toList-vmap f v)

  vmap-lemma
    : {k : ℕ}{A B : Set}{f : A → B}{g : B → A}
    → (v : Vec A k)
    → (∀ x → g (f x) ≡ x)
    → vmap g (vmap f v) ≡ v
  vmap-lemma [] prf      = refl
  vmap-lemma (x ∷ k) prf = cong₂ _∷_ (prf x) (vmap-lemma k prf)

  vsplit : {n : ℕ}{A : Set}(m : ℕ) 
         → Vec A (m + n) → Vec A m × Vec A n
  vsplit zero v          = [] , v
  vsplit (suc m) (x ∷ v) = x ∷ p1 (vsplit m v) , p2 (vsplit m v)

  vsplit-elim
    : {m n : ℕ}{A : Set}(l₁ l₂ : List A)
      {p : length (l₁ ++ l₂) ≡ m + n}
      {q₁ : length l₁ ≡ m}{q₂ : length l₂ ≡ n}
    → vsplit m (vec (l₁ ++ l₂) p) ≡ (vec l₁ q₁ , vec l₂ q₂)
  vsplit-elim [] l2 {q₁ = refl} {q₂} 
    = cong (_,_ []) (vec-reduce l2)
  vsplit-elim (x ∷ l1) l2 {q₁ = refl} {q₂} 
    = cong (λ P → x ∷ p1 P , p2 P) (vsplit-elim l1 l2)

  vsplit-lemma 
    : {m n : ℕ}{A : Set}(v1 : Vec A m)(v2 : Vec A n)(vres : Vec A (m + n))
    → vsplit m vres ≡ (v1 , v2)
    → vres ≡ (v1 ++v v2)
  vsplit-lemma [] v2 .v2 refl = refl
  vsplit-lemma {suc m} {n} (v ∷ ._) ._ (.v ∷ vres) refl 
    = cong (_∷_ v) (vsplit-lemma (p1 (vsplit m vres)) (p2 (vsplit m vres)) vres refl)

  private
    length-elim-1 
      : {n m : ℕ}{A : Set}(l1 l2 : List A)
      → length l1 ≡ m
      → length (l1 ++ l2) ≡ m + n
      → length l2 ≡ n
    length-elim-1 l1 l2 refl q 
      rewrite length-++ l1 {ys = l2}
           = +-inj-1 {m = length l1} q

    length-elim-2
      : {n m : ℕ}{A : Set}(l1 l2 : List A)
      → length l2 ≡ n
      → length (l1 ++ l2) ≡ m + n
      → length l1 ≡ m
    length-elim-2 l1 l2 refl q 
      rewrite length-++ l1 {ys = l2}
           = +-inj-2 {m = length l2} q

  vsplit-elim-1 
    : {m n : ℕ}{A : Set}(l₁ l₂ : List A)
      {p : length (l₁ ++ l₂) ≡ m + n}
      {q : length l₁ ≡ m}
    → p1 (vsplit m (vec (l₁ ++ l₂) p)) ≡ vec l₁ q
  vsplit-elim-1 l1 l2 {p} {q}
    rewrite vsplit-elim l1 l2 {p} {q} {length-elim-1 l1 l2 q p}
      = refl

  vsplit-elim-2
    : {m n : ℕ}{A : Set}(l₁ l₂ : List A)
      {p : length (l₁ ++ l₂) ≡ m + n}
      {q : length l₂ ≡ n}
    → p2 (vsplit m (vec (l₁ ++ l₂) p)) ≡ vec l₂ q
  vsplit-elim-2 {m} l1 l2 {p} {q}
    rewrite vsplit-elim {m} l1 l2 {p} {length-elim-2 l1 l2 q p} {q}
      = refl

  toList-vsplit-++
    : {m n : ℕ}{A : Set}(as : Vec A (m + n))
    → toList as ≡ toList (p1 (vsplit m as)) ++ toList (p2 (vsplit m as))
  toList-vsplit-++ {zero} as = refl
  toList-vsplit-++ {suc m} (x ∷ as) 
    = cong (_∷_ x) (toList-vsplit-++ {m = m} as)

  map-toList-lemma
    : {m : ℕ}{A B : Set}(as : Vec A m)
    → (f : A → B)
    → map f (toList as) ≡ toList (vmap f as)
  map-toList-lemma [] f = refl
  map-toList-lemma (x ∷ as) f 
    = cong (_∷_ (f x)) (map-toList-lemma as f)
