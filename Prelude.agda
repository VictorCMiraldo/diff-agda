-- A Simple selection of modules with some renamings to
-- make my (your) life easier when starting a new agda module.
--
-- This includes standard functionality to work on:
--  1. Functions,
--  2. Naturals,
--  3. Products and Coproducts (projections and injections are p1, p2, i1, i2).
--  4. Finite Types (zero and suc are fz and fs)
--  5. Lists
--  6. Booleans and PropositionalEquality
--  7. Decidable Predicates
--
module Prelude where

  open import Level
    renaming (zero to lz; suc to ls)
    public

  open import Data.Unit.NonEta
    using (Unit; unit)
    public

  open import Data.Empty
    using (⊥; ⊥-elim)
    public

  open import Function
    using (_∘_; _$_; flip; id; const; _on_)
    public

  open import Data.Nat
    using (ℕ; suc; zero; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
    renaming (_≟_ to _≟-ℕ_; _≤?_ to _≤?-ℕ_
             ; compare to compareℕ; Ordering to Ordℕ
             ; less to LE ; greater to GE ; equal to EQ)
    public

  open import Data.Fin
    using (Fin; fromℕ; fromℕ≤; toℕ)
    renaming (zero to fz; suc to fs;
              inject+ to finject; raise to fraise)
    public

  open import Data.Fin.Properties
    using ()
    renaming (_≟_ to _≟-Fin_)
    public

  open import Data.List
    using (List; _∷_; []; map; _++_; zip; filter;
           all; any; concat; foldr; reverse; length;
           sum)
    public

  open import Data.Product
    using (∃; Σ; _×_; _,_; uncurry; curry)
    renaming (proj₁ to p1; proj₂ to p2
           ; <_,_> to split)
    public

  open import Data.Sum
    using (_⊎_; [_,_]′)
    renaming (inj₁ to i1; inj₂ to i2
           ; [_,_] to either)
    public

  open import Data.Bool
    using (Bool; true; false; if_then_else_; not)
    renaming (_∧_ to _and_; _∨_ to _or_)
    public

  open import Relation.Nullary
    using (Dec; yes; no; ¬_)
    public

  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong; cong₂; subst)
    renaming (proof-irrelevance to ≡-pi)
    public

  open import Relation.Binary.PropositionalEquality.TrustMe
    hiding (trustMe)
    renaming (erase to ∅_)
    public

  open import Data.Maybe
    using (Maybe; just; nothing)
    renaming (maybe′ to maybe)
    public

  {- Usefull List Processing -}

  lsplit : ∀{a}{A : Set a}(n : ℕ)(l : List A) → List A × List A
  lsplit zero l          = [] , l
  lsplit (suc n) []      = [] , []
  lsplit (suc n) (x ∷ l) 
    = let li , lo = lsplit n l
       in x ∷ li , lo

  lsplit-++-lemma
    : ∀{a}{A : Set a}(l1 l2 : List A) 
    → lsplit (length l1) (l1 ++ l2) ≡ (l1 , l2)
  lsplit-++-lemma [] l2 = refl
  lsplit-++-lemma (x ∷ l1) l2 
    rewrite lsplit-++-lemma l1 l2 
          = refl

  lsplit-length-lemma
    : ∀{a}{A : Set a}(l : List A)
    → (m n : ℕ)
    → m + n ≤ length l
    → m ≤ length (p1 (lsplit m l))
    × n ≤ length (p2 (lsplit m l))
  lsplit-length-lemma l zero n hip = z≤n , hip
  lsplit-length-lemma [] (suc m) n ()
  lsplit-length-lemma (x ∷ l) (suc m) n (s≤s hip) 
    = let r1 , r2 = lsplit-length-lemma l m n hip
       in (s≤s r1) , r2
    

  lhead : ∀{a}{A : Set a} → List A → Maybe A
  lhead []      = nothing
  lhead (x ∷ _) = just x

  map-lemma : {A B : Set}{f : A → B}{g : B → A}
            → (l : List A)
            → (∀ x → g (f x) ≡ x)
            → map g (map f l) ≡ l
  map-lemma [] prf      = refl
  map-lemma (x ∷ l) prf = cong₂ _∷_ (prf x) (map-lemma l prf)

  {- Some Propositional Logic -}
  
  _iff_ : Set → Set → Set
  A iff B = (A → B) × (B → A)

  {- Usefull Predicates -}

  So : Bool → Set
  So true  = Unit
  So false = ⊥

  dec-elim : ∀{a b}{A : Set a}{B : Set b}
           → (A → B) → (¬ A → B) → Dec A → B
  dec-elim f g (yes p) = f p
  dec-elim f g (no  p) = g p

  dec2set : ∀{a}{A : Set a} → Dec A → Set
  dec2set (yes _) = Unit
  dec2set (no  _) = ⊥

  isTrue : ∀{a}{A : Set a} → Dec A → Bool
  isTrue (yes _) = true
  isTrue _       = false

  takeWhile : ∀{a}{A : Set a} → (A → Bool) → List A → List A
  takeWhile _ [] = []
  takeWhile f (x ∷ xs) with f x
  ...| true = x ∷ takeWhile f xs
  ...| _    = takeWhile f xs

  {- Some Maybe functionality -}

  data Is-Just {a}{A : Set a} : Maybe A → Set a where
    indeed : (x : A) → Is-Just (just x)

  from-Just : ∀{a}{A : Set a}{x : Maybe A} → Is-Just x → A
  from-Just (indeed x) = x

  Is-Just-≡ : ∀{a}{A : Set a}{x : Maybe A} → Is-Just x → Σ A (λ k → x ≡ just k)
  Is-Just-≡ (indeed x) = x , refl

  ≡-Is-Just : ∀{a}{A : Set a}{x : Maybe A}{k : A} → x ≡ just k → Is-Just x
  ≡-Is-Just {k = k} refl = indeed k

  Is-Just-⊥ : ∀{a}{A : Set a}{x : A} 
            → (Is-Just (just x) → Is-Just {A = A} nothing) → ⊥
  Is-Just-⊥ {x = x} f with f (indeed x) 
  ...| ()

  just-inj : ∀{a}{A : Set a}{x y : A}
           → _≡_ {a} {Maybe A} (just x) (just y) → x ≡ y
  just-inj refl = refl

  Maybe-⊥ : ∀{a}{A : Set a}{x : A}
          → _≡_ {a} {Maybe A} (just x) nothing
          → ⊥
  Maybe-⊥ ()

  {- Maybe is applicative! And here are some very usefull lemmas -}

  _<M>_ : ∀{a b}{A : Set a}{B : Set b} 
        → (A → B) → Maybe A → Maybe B
  f <M> nothing  = nothing
  f <M> just x   = just (f x)

  <M>-elim : ∀{a b}{A : Set a}{B : Set b}
              {f : A → B}{x : Maybe A}{kb : B}
           → f <M> x ≡ just kb
           → Σ A (λ ka → kb ≡ f ka × x ≡ just ka)
  <M>-elim {x = nothing} ()
  <M>-elim {x = just y} refl = y , (refl , refl)

  <M>-Is-Just : ∀{a b}{A : Set a}{B : Set b}
                {f : A → B}{x : Maybe A}
              → Is-Just (f <M> x) → Is-Just x
  <M>-Is-Just {x = nothing} ()
  <M>-Is-Just {x = just x} _ = indeed x

  Is-Just-<M> : ∀{a b}{A : Set a}{B : Set b}
                {f : A → B}{x : Maybe A}
               → Is-Just x → Is-Just (f <M> x)
  Is-Just-<M> {x = nothing} ()
  Is-Just-<M> {f = f} {x = just x} (indeed .x) = indeed (f x)

  <M>-intro : ∀{a b}{A : Set a}{B : Set b}
              {f : A → B}{x : Maybe A}{k : A}
            → x ≡ just k
            → f <M> x ≡ just (f k)
  <M>-intro refl = refl

  _<M*>_ : ∀{a b}{A : Set a}{B : Set b} 
         → Maybe (A → B) → Maybe A → Maybe B
  _       <M*> nothing = nothing
  nothing <M*> just _  = nothing
  just f  <M*> just x  = just (f x)

  Is-Just-<M*> : ∀{a b}{A : Set a}{B : Set b}
                 {f : Maybe (A → B)}{x : Maybe A}
               → Is-Just f → Is-Just x → Is-Just (f <M*> x)
  Is-Just-<M*> {f = nothing} () _
  Is-Just-<M*> {x = nothing} _ ()
  Is-Just-<M*> {f = just f} {x = just x} _ _ = indeed (f x)

  <M*>-nothing : ∀{a b}{A : Set a}{B : Set b}{x : Maybe A}
               → nothing {A = A → B} <M*> x ≡ nothing
  <M*>-nothing {x = nothing} = refl
  <M*>-nothing {x = just _ } = refl

  <M*>-elim : ∀{a b}{A : Set a}{B : Set b}
              {f : Maybe (A → B)}{x : Maybe A}{kb : B}
            → f <M*> x ≡ just kb
            → Σ ((A → B) × A) (λ fa → f ≡ just (p1 fa) × kb ≡ (p1 fa) (p2 fa))
  <M*>-elim {f = f} {x = nothing} ()
  <M*>-elim {f = nothing} {x = just _} ()
  <M*>-elim {f = just f}  {x = just x} {.(f x)} refl = (f , x) , (refl , refl)

  <M*>-elim-full : ∀{a b}{A : Set a}{B : Set b}
                    {f : Maybe (A → B)}{x : Maybe A}{kb : B}
            → f <M*> x ≡ just kb
            → Σ ((A → B) × A) 
                (λ fa → f ≡ just (p1 fa) × kb ≡ (p1 fa) (p2 fa) × x ≡ just (p2 fa))
  <M*>-elim-full {f = f} {x = nothing} ()
  <M*>-elim-full {f = nothing} {x = just _} ()
  <M*>-elim-full {f = just f}  {x = just x} {.(f x)} refl = (f , x) , (refl , (refl , refl))

  <M*>-to-<M> : ∀{a b}{A : Set a}{B : Set b}
                {f : A → B}{x : Maybe A}{kb : B}
              → just f <M*> x ≡ just kb
              → f <M> x ≡ just kb
  <M*>-to-<M> {x = nothing} ()
  <M*>-to-<M> {x = just x} prf = prf

  <M>-to-<M*> : ∀{a b}{A : Set a}{B : Set b}
                {f : A → B}{x : Maybe A}{kb : B}
              → f <M> x ≡ just kb
              → just f <M*> x ≡ just kb
  <M>-to-<M*> {x = nothing} ()
  <M>-to-<M*> {x = just x} prf = prf

  infixl 20 _<M>_ _<M*>_

  {- Function Extensionality comes in fairly handy regurlaly -}

  postulate
    fun-ext : ∀{a b}{A : Set a}{B : Set b}{f g : A → B}
            → (∀ x → f x ≡ g x)
            → f ≡ g

  ¬≡-pi : ∀{a}{A : Set a}{a₁ a₂ : A}
        → (p q : ¬ (a₁ ≡ a₂)) → p ≡ q
  ¬≡-pi p q = fun-ext (λ x → ⊥-elim (p x))

  -- Some minor boilerplate to solve equality problem...
  record Eq (A : Set) : Set where
    constructor eq
    field cmp : (x y : A) → Dec (x ≡ y)

  open Eq {{...}}

  record Enum (A : Set) : Set where
    constructor enum
    field
      toEnum   : A → Maybe ℕ
      fromEnum : ℕ → Maybe A

  open Enum {{...}}

  instance
    eq-ℕ : Eq ℕ
    eq-ℕ = eq _≟-ℕ_

    enum-ℕ : Enum ℕ
    enum-ℕ = enum just just

    eq-Fin : ∀{n} → Eq (Fin n)
    eq-Fin = eq _≟-Fin_

    enum-Fin : ∀{n} → Enum (Fin n)
    enum-Fin {n} = enum (λ x → just (toℕ x)) fromℕ-partial
      where
        fromℕ-partial : ℕ → Maybe (Fin n)
        fromℕ-partial m with suc m ≤?-ℕ n
        ...| yes prf = just (fromℕ≤ {m} {n} prf)
        ...| no  _   = nothing

    eq-⊥ : Eq ⊥
    eq-⊥ = eq (λ x → ⊥-elim x)

    enum-⊥ : Enum ⊥
    enum-⊥ = enum ⊥-elim (const nothing)

    eq-Maybe : ∀{A} ⦃ eqA : Eq A ⦄ → Eq (Maybe A)
    eq-Maybe = eq decide
      where
        decide : {A : Set} ⦃ eqA : Eq A ⦄
               → (x y : Maybe A) → Dec (x ≡ y)
        decide nothing nothing   = yes refl
        decide nothing (just _)  = no (λ ())
        decide (just _) nothing  = no (λ ())
        decide ⦃ eq f ⦄ (just x) (just y) with f x y
        ...| yes x≡y = yes (cong just x≡y)
        ...| no  x≢y = no (x≢y ∘ just-inj)

    enum-Maybe : ∀{A} ⦃ enA : Enum A ⦄ → Enum (Maybe A)
    enum-Maybe ⦃ enum aℕ ℕa ⦄ = enum (maybe aℕ nothing) (just ∘ ℕa)

    eq-List : {A : Set}{{eq : Eq A}} → Eq (List A)
    eq-List {A} {{eq _≟_}} = eq decide
      where
        open import Data.List.Properties
          renaming (∷-injective to ∷-inj)

        decide : (a b : List A) → Dec (a ≡ b)
        decide [] (_ ∷ _) = no (λ ())
        decide (_ ∷ _) [] = no (λ ())
        decide []   []    = yes refl
        decide (a ∷ as) (b ∷ bs)
          with a ≟ b | decide as bs
        ...| yes a≡b | yes as≡bs
          rewrite a≡b = yes (cong (_∷_ b) as≡bs)
        ...| no  a≢b | yes as≡bs = no (a≢b ∘ p1 ∘ ∷-inj)
        ...| yes a≡b | no  as≢bs = no (as≢bs ∘ p2 ∘ ∷-inj)
        ...| no  a≢b | no  as≢bs = no (a≢b ∘ p1 ∘ ∷-inj)
