open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff

module Diffing.Patches.Diff.Functor where

  {-
    This module defines some functorial functionality for
    X ↦ D X t ty, for fixed t and ty.

    The proofs are trivial, it's just a matter of exhausting
    Agda's case analysis.
  -}

  -- D-map definition
  mutual
    {-# TERMINATING #-}
    D-map : ∀{a b}{n : ℕ}{t : Tel n}{ty : U n}{A : Set a}{B : Set b} 
          → (A → B) → D A t ty → D B t ty
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

    Dμ-map : ∀{a b}{n : ℕ}{t : Tel n}{ty : U (suc n)}{A : Set a}{B : Set b} 
           → (A → B) → List (Dμ A t ty) → List (Dμ B t ty)
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
                 {A : Set a}{B : Set b}{C : Set c}
                 (f : B → C)(g : A → B)(d : D A t ty)
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
                  {A : Set a}{B : Set b}{C : Set c}
                  (f : B → C)(g : A → B)(d : List (Dμ A t ty))
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
    D-map-id : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}{A : Set a}
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

    Dμ-map-id : ∀{a}{n : ℕ}{t : Tel n}{ty : U (suc n)}{A : Set a}
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
  mutual
    forget : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}{A : Set a} 
           → D A t ty → List A
    forget (D-A x) = x ∷ []
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

    forgetμ : ∀{a}{n : ℕ}{t : Tel n}{ty : U (suc n)}{A : Set a} 
            → List (Dμ A t ty) → List A
    forgetμ [] = []
    forgetμ (Dμ-A a ∷ ds)      = a ∷ forgetμ ds
    forgetμ (Dμ-dwn _ dx ∷ ds) = forget dx ++ forgetμ ds
    forgetμ (_ ∷ ds)           = forgetμ ds


  {- forget is a natural transformation -}
  mutual
    forget-natural : ∀{a b}{n : ℕ}{t : Tel n}{ty : U n}{A : Set a}{B : Set b}
                   → (f : A → B)(d : D A t ty)
                   → forget (D-map f d) ≡ map f (forget d)
    forget-natural = trustme
      where
        postulate trustme : ∀{a}{A : Set a} → A

  -- forget is obviously natural, that is:
  --
  --   forget ∘ D-map f ≡ map f ∘ forget
  --
  -- But since there is no need for this fact, yet,
  -- we leave it unstated.

  {- Some usefull casting operations -}

  cast : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}{A : Set a}
       → Patch t ty → D A t ty
  cast = D-map (λ ())

  castμ : ∀{a}{n : ℕ}{t : Tel n}{ty : U (suc n)}{A : Set a}
        → Patchμ t ty → List (Dμ A t ty)
  castμ = Dμ-map (λ ())

  {- We can always "uncast" a (D A) to a Patch as long 
     as it doesn't have any (D-A _) inside.
  -}

  open import Diffing.Utils.Propositions using (++-[])
  mutual
    uncast : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}{A : Set a}
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

    uncastμ : ∀{a}{n : ℕ}{t : Tel n}{ty : U (suc n)}{A : Set a}
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
  D-map-cast : ∀{a b}{n : ℕ}{t : Tel n}{ty : U n}
                {A : Set a}{B : Set b}
                (f : A → B)(d : Patch t ty)
              → D-map f (cast d) ≡ cast d
  D-map-cast f d 
    = trans (D-map-join f (λ ()) d) 
            (cong (λ P → D-map P d) (fun-ext (λ ())))

  {- Forgettting a cast'ed value is the empty list -}
  forget-cast : ∀{a}{n : ℕ}{t : Tel n}{ty : U n}{A : Set a}
                (d : Patch t ty)
              → forget {A = A} (cast d) ≡ []
  forget-cast = trustme
      where
        postulate trustme : ∀{a}{A : Set a} → A
