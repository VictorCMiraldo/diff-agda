open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches1.Diff
open import Function using (_∋_)

module Diffing.Patches1.Diff.Functor where

  {-
    This module defines some functorial functionality for
    X ↦ D X t ty, for fixed t and ty.

    The proofs are trivial, it's just a matter of exhausting
    Agda's case analysis.
  -}

  -- D-map definition
  mutual
    {-# TERMINATING #-}
    D-map : ∀{a b}{n : ℕ}{t : Tel n}{ty : U n}
             {A : {n : ℕ} → Tel n → U n → Set a}
             {B : {n : ℕ} → Tel n → U n → Set b} 
          → ({m : ℕ}{t' : Tel m}{ty' : U m} → A t' ty' → B t' ty') 
          → D A t ty → D B t ty
    D-map f (D-A x) = D-A (f x)
    D-map f D-id   = D-id
    D-map f D-void = D-void
    D-map f (D-inl d) = D-inl (D-map f d)
    D-map f (D-inr d) = D-inr (D-map f d)
    D-map f (D-setl x x₁) = D-setl x x₁
    D-map f (D-setr x x₁) = D-setr x x₁
    D-map f (D-pair d d₁) = D-pair (D-map f d) (D-map f d₁)
    D-map f (D-mu x) = D-mu (Dμ-map f x)
    D-map f (D-β d) = D-β (D-map f d)
    D-map f (D-top d) = D-top (D-map f d)
    D-map f (D-pop d) = D-pop (D-map f d)

    Dμ-map : ∀{a b}{n : ℕ}{t : Tel n}{ty : U (suc n)}
             {A : {n : ℕ} → Tel n → U n → Set a}
             {B : {n : ℕ} → Tel n → U n → Set b} 
           → ({m : ℕ}{t' : Tel m}{ty' : U m} → A t' ty' → B t' ty')
           → List (Dμ A t ty) → List (Dμ B t ty)
    Dμ-map f [] = []
    Dμ-map f (Dμ-A x   ∷ d) = Dμ-A (f x) ∷ Dμ-map f d
    Dμ-map f (Dμ-ins x ∷ d) = Dμ-ins x ∷ Dμ-map f d
    Dμ-map f (Dμ-cpy x ∷ d) = Dμ-cpy x ∷ Dμ-map f d
    Dμ-map f (Dμ-del x ∷ d) = Dμ-del x ∷ Dμ-map f d
    Dμ-map f (Dμ-dwn x dx ∷ d) 
      = Dμ-dwn x (D-map f dx) ∷ Dμ-map f d

  --
  -- D-map preserves composition
  --
  mutual
    D-map-join : ∀{a b c}{n : ℕ}{t : Tel n}{ty : U n}
                 {A : {n : ℕ} → Tel n → U n → Set a}
                 {B : {n : ℕ} → Tel n → U n → Set b}
                 {C : {n : ℕ} → Tel n → U n → Set c}
                 (f : {m : ℕ}{t' : Tel m}{ty' : U m} → B t' ty' → C t' ty')
                 (g : {m : ℕ}{t' : Tel m}{ty' : U m} → A t' ty' → B t' ty')
                 (d : D A t ty)
               → D-map f (D-map g d) ≡ D-map (f ∘ g) d
    D-map-join f g (D-A x) = refl
    D-map-join f g D-id   = refl
    D-map-join f g D-void = refl
    D-map-join f g (D-inl d) = cong D-inl (D-map-join f g d)
    D-map-join f g (D-inr d) = cong D-inr (D-map-join f g d)
    D-map-join f g (D-setl x y) = refl
    D-map-join f g (D-setr x y) = refl
    D-map-join f g (D-pair d e) 
      = cong₂ D-pair (D-map-join f g d) (D-map-join f g e)
    D-map-join f g (D-β d) = cong D-β (D-map-join f g d)
    D-map-join f g (D-top d) = cong D-top (D-map-join f g d)
    D-map-join f g (D-pop d) = cong D-pop (D-map-join f g d)
    D-map-join f g (D-mu x) = cong D-mu (Dμ-map-join f g x)

    Dμ-map-join : ∀{a b c}{n : ℕ}{t : Tel n}{ty : U (suc n)}
                  {A : {n : ℕ} → Tel n → U n → Set a}
                  {B : {n : ℕ} → Tel n → U n → Set b}
                  {C : {n : ℕ} → Tel n → U n → Set c}
                  (f : {m : ℕ}{t' : Tel m}{ty' : U m} → B t' ty' → C t' ty')
                  (g : {m : ℕ}{t' : Tel m}{ty' : U m} → A t' ty' → B t' ty')
                  (d : List (Dμ A t ty))
               → Dμ-map f (Dμ-map g d) ≡ Dμ-map (f ∘ g) d
    Dμ-map-join f g [] = refl
    Dμ-map-join f g (Dμ-A x ∷ d) = cong (_∷_ (Dμ-A (f (g x)))) (Dμ-map-join f g d)
    Dμ-map-join f g (Dμ-ins x ∷ d) = cong (_∷_ (Dμ-ins x)) (Dμ-map-join f g d)
    Dμ-map-join f g (Dμ-del x ∷ d) = cong (_∷_ (Dμ-del x)) (Dμ-map-join f g d)
    Dμ-map-join f g (Dμ-cpy x ∷ d) = cong (_∷_ (Dμ-cpy x)) (Dμ-map-join f g d)
    Dμ-map-join f g (Dμ-dwn x dx ∷ d) 
      = cong₂ (λ P Q → Dμ-dwn x P ∷ Q) (D-map-join f g dx) (Dμ-map-join f g d)

  --
  -- And identities
  --
  mutual
    D-map-id : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}
               {A : {n : ℕ} → Tel n → U n → Set a}
               (d : D A t ty)
             → D-map id d ≡ d
    D-map-id (D-A x) = refl
    D-map-id D-id   = refl
    D-map-id D-void = refl
    D-map-id (D-inl d) = cong D-inl (D-map-id d)
    D-map-id (D-inr d) = cong D-inr (D-map-id d)
    D-map-id (D-setl x y) = refl
    D-map-id (D-setr x y) = refl
    D-map-id (D-pair d e) = cong₂ D-pair (D-map-id d) (D-map-id e)
    D-map-id (D-β d) = cong D-β (D-map-id d)
    D-map-id (D-top d) = cong D-top (D-map-id d)
    D-map-id (D-pop d) = cong D-pop (D-map-id d)
    D-map-id (D-mu x) = cong D-mu (Dμ-map-id x)

    Dμ-map-id : ∀{a}{n : ℕ}{t : Tel n}{ty : U (suc n)}
                {A : {n : ℕ} → Tel n → U n → Set a}
                (d : List (Dμ A t ty)) → Dμ-map id d ≡ d
    Dμ-map-id [] = refl
    Dμ-map-id (Dμ-A x ∷ d) = cong (_∷_ (Dμ-A x)) (Dμ-map-id d)
    Dμ-map-id (Dμ-ins x ∷ d) = cong (_∷_ (Dμ-ins x)) (Dμ-map-id d)
    Dμ-map-id (Dμ-del x ∷ d) = cong (_∷_ (Dμ-del x)) (Dμ-map-id d)
    Dμ-map-id (Dμ-cpy x ∷ d) = cong (_∷_ (Dμ-cpy x)) (Dμ-map-id d)
    Dμ-map-id (Dμ-dwn x dx ∷ d) 
      = cong₂ (λ P Q → Dμ-dwn x P ∷ Q) (D-map-id dx) (Dμ-map-id d)

  --
  -- Here we define a forgetful functor from D's to Lists.
  --

  {-
    Idea for the future: Use type-indexed lists for forget
  -}
  {-
  TypeI : Set
  TypeI = Σ ℕ (λ n → Tel n × U n)

  data TypedList {a}(A : {n : ℕ} → Tel n → U n → Set a)
         : List TypeI → Set a where
    []t  : TypedList A []
    _∷t_ : {n : ℕ}{t : Tel n}{ty : U n}{l : List TypeI}
         → A t ty → TypedList A l → TypedList A ((n , (t , ty)) ∷ l)

  mutual
    forgetᵢ : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}
              {A : {n : ℕ} → Tel n → U n → Set a}
            → D A t ty → Σ (List TypeI) (TypedList A)
    forgetᵢ d = {!!}
  -}

  data ↓_ {a}(A : {n : ℕ} → Tel n → U n → Set a) : Set a where
    unIdx : {n : ℕ}{t : Tel n}{ty : U n} → A t ty → ↓ A

  ↓-map : ∀{a b}{B : Set b}{A : {n : ℕ} → Tel n → U n → Set a}
          (f : {n : ℕ}{t : Tel n}{ty : U n} → A t ty → B)
        → ↓ A → B
  ↓-map f (unIdx a) = f a

  ↓-map-↓ : ∀{a b}
          {A : {n : ℕ} → Tel n → U n → Set a}
          {B : {n : ℕ} → Tel n → U n → Set b}
          (f : {n : ℕ}{t : Tel n}{ty : U n} → A t ty → B t ty)
          → ↓ A → ↓ B
  ↓-map-↓ f (unIdx a) = unIdx (f a)

  mutual
    forget : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}
             {A : {n : ℕ} → Tel n → U n → Set a}
           → D A t ty → List (↓ A)
    forget (D-A {n} {t} {ty} x) = unIdx x ∷ []
    forget D-id   = []
    forget D-void = []
    forget (D-inl d) = forget d
    forget (D-inr d) = forget d
    forget (D-setl x x₁) = []
    forget (D-setr x x₁) = []
    forget (D-pair d d₁) = forget d ++ forget d₁
    forget (D-β d) = forget d
    forget (D-top d) = forget d
    forget (D-pop d) = forget d
    forget (D-mu x) = forgetμ x

    forgetμ : ∀{a}{n : ℕ}{t : Tel n}{ty : U (suc n)}
              {A : {n : ℕ} → Tel n → U n → Set a}
            → List (Dμ A t ty) → List (↓ A)
    forgetμ [] = []
    forgetμ (Dμ-A x ∷ ds)      = unIdx x ∷ forgetμ ds
    forgetμ (Dμ-dwn _ dx ∷ ds) = forget dx ++ forgetμ ds
    forgetμ (_ ∷ ds)           = forgetμ ds

  
  {-
  {- forget is a natural transformation -}
  mutual
    forget-natural : ∀{a b}{n : ℕ}{t : Tel n}{ty : U n}
                     {A : {n : ℕ} → Tel n → U n → Set a}
                     {B : {n : ℕ} → Tel n → U n → Set b}
                   → (f : {m : ℕ}{t' : Tel m}{ty' : U m} → A t' ty' → B t' ty')
                   → (d : D A t ty)
                   → forget (D-map f d) ≡ map {!!} (forget d)
    forget-natural = trustme
      where
        postulate trustme : ∀{a}{A : Set a} → A
  -}

  -- forget is obviously natural, that is:
  --
  --   forget ∘ D-map f ≡ map f ∘ forget
  --
  -- But since there is no need for this fact, yet,
  -- we leave it unstated.

  {- Some usefull casting operations -}

  cast : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}
         {A : {n : ℕ} → Tel n → U n → Set a}
       → Patch t ty → D A t ty
  cast {A = A} = D-map (({m : ℕ}{t : Tel m}{ty : U m} → ⊥ → A t ty) ∋ (λ ()))

  castμ : ∀{a}{n : ℕ}{t : Tel n}{ty : U (suc n)}
          {A : {n : ℕ} → Tel n → U n → Set a}
        → Patchμ t ty → List (Dμ A t ty)
  castμ {A = A} = Dμ-map (({m : ℕ}{t : Tel m}{ty : U m} → ⊥ → A t ty) ∋ (λ ()))

  {- We can always "uncast" a (D A) to a Patch as long 
     as it doesn't have any (D-A _) inside.
  -}

  open import Diffing.Utils.Propositions using (++-[])
  mutual
    uncast : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}
             {A : {n : ℕ} → Tel n → U n → Set a}
           → (d : D A t ty) → forget d ≡ []
           → Patch t ty
    uncast (D-A x) ()
    uncast D-id prf = D-id
    uncast D-void prf = D-void
    uncast (D-inl d) prf = D-inl (uncast d prf)
    uncast (D-inr d) prf = D-inr (uncast d prf)
    uncast (D-setl x x₁) prf = D-setl x x₁
    uncast (D-setr x x₁) prf = D-setr x x₁
    uncast (D-pair d e) prf 
      = D-pair (uncast d (p1 (++-[] prf))) 
               (uncast e (p2 (++-[] {l = forget d} prf)))
    uncast (D-mu x) prf = D-mu (uncastμ x prf)
    uncast (D-β d) prf = D-β (uncast d prf)
    uncast (D-top d) prf = D-top (uncast d prf)
    uncast (D-pop d) prf = D-pop (uncast d prf)

    uncastμ : ∀{a}{n : ℕ}{t : Tel n}{ty : U (suc n)}
             {A : {n : ℕ} → Tel n → U n → Set a}
           → (d : List (Dμ A t ty)) → forgetμ d ≡ []
           → Patchμ t ty
    uncastμ [] prf = []
    uncastμ (Dμ-A x ∷ d) ()
    uncastμ (Dμ-ins x ∷ d) prf = Dμ-ins x ∷ uncastμ d prf
    uncastμ (Dμ-del x ∷ d) prf = Dμ-del x ∷ uncastμ d prf
    uncastμ (Dμ-cpy x ∷ d) prf = Dμ-cpy x ∷ uncastμ d prf
    uncastμ (Dμ-dwn x dx ∷ d) prf with ++-[] {l = forget dx} prf 
    ...| p1 , p2 = Dμ-dwn x (uncast dx p1) ∷ uncastμ d p2

  {- Mapping over a "casted" value is doing nothing. -}
  D-map-cast : ∀{a b}{k : ℕ}{t : Tel k}{ty : U k}
                {A : {n : ℕ} → Tel n → U n → Set a}
                {B : {n : ℕ} → Tel n → U n → Set b}
                (f : {m : ℕ}{t' : Tel m}{ty' : U m} → A t' ty' → B t' ty')
                (d : Patch t ty)
              → D-map (λ {k} {t} {ty} x → f {k} {t} {ty} x) (cast d) ≡ cast d
  D-map-cast {A = A} {B = B} f d 
    = trans (D-map-join f (λ ()) d) 
            (cong₂ D-map 
              (cong id trustme)
            refl)
    where
      postulate trustme : ∀{a}{A : Set a} → A
      
  

  {- Forgettting a cast'ed value is the empty list -}
  forget-cast : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}
                {A : {n : ℕ} → Tel n → U n → Set a}
                (d : Patch t ty)
              → forget {A = A} (cast d) ≡ []
  forget-cast = trustme
      where
        postulate trustme : ∀{a}{A : Set a} → A


  {- Monadic Multiplication -}
  {- Idea:
     Represent D-id inside the parameter, as (1 + A)
  -}
  mutual
    D-mult : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}
             {A : {k : ℕ} → Tel k → U k → Set a}
           → D (D A) t ty → D A t ty
    D-mult (D-A d) = d
    D-mult D-id = D-id
    D-mult D-void = D-id
    D-mult (D-inl d) = D-inl (D-mult d)
    D-mult (D-inr d) = D-inr (D-mult d)
    D-mult (D-setl x x₁) = D-setl x x₁
    D-mult (D-setr x x₁) = D-setr x x₁
    D-mult (D-pair d d₁) = D-pair (D-mult d) (D-mult d₁)
    D-mult (D-mu x) = D-mu (Dμ-mult x)
    D-mult (D-β d) = D-β (D-mult d)
    D-mult (D-top d) = D-top (D-mult d)
    D-mult (D-pop d) = D-pop (D-mult d)

    Dμ-mult : ∀{a}{n : ℕ}{t : Tel n}{ty : U (suc n)}
             {A : {k : ℕ} → Tel k → U k → Set a}
           → List (Dμ (D A) t ty) → List (Dμ A t ty)
    Dμ-mult [] = []
    Dμ-mult (Dμ-A (D-A x) ∷ l) = Dμ-A x ∷ Dμ-mult l
    -- TODO: I think a D-id inside a Dμ-A should become a Dμ-Id
    Dμ-mult (Dμ-A D-id ∷ l) = Dμ-mult l
    Dμ-mult (Dμ-A (D-mu x) ∷ l) = x ++ Dμ-mult l
    Dμ-mult (Dμ-ins x ∷ l) = Dμ-ins x ∷ Dμ-mult l
    Dμ-mult (Dμ-del x ∷ l) = Dμ-del x ∷ Dμ-mult l
    Dμ-mult (Dμ-cpy x ∷ l) = Dμ-cpy x ∷ Dμ-mult l
    Dμ-mult (Dμ-dwn x x₁ ∷ l) = Dμ-dwn x (D-mult x₁) ∷ Dμ-mult l