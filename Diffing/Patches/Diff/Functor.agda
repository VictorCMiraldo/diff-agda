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
    D-map : {n : ℕ}{t : Tel n}{ty : U n}{A B : Set} 
          → (A → B) → D A t ty → D B t ty
    D-map f (D-A x) = D-A (f x)
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

    Dμ-map : {n : ℕ}{t : Tel n}{ty : U (suc n)}{A B : Set} 
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
    D-map-join : {n : ℕ}{t : Tel n}{ty : U n}{A B C : Set}
                 (f : B → C)(g : A → B)(d : D A t ty)
               → D-map f (D-map g d) ≡ D-map (f ∘ g) d
    D-map-join f g (D-A x) = refl
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

    Dμ-map-join : {n : ℕ}{t : Tel n}{ty : U (suc n)}{A B C : Set}
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
    D-map-id : {n : ℕ}{t : Tel n}{ty : U n}{A : Set}(d : D A t ty)
             → D-map id d ≡ d
    D-map-id (D-A x) = refl
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

    Dμ-map-id : {n : ℕ}{t : Tel n}{ty : U (suc n)}{A : Set}
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
    forget : {n : ℕ}{t : Tel n}{ty : U n}{A : Set} 
           → D A t ty → List A
    forget (D-A x) = x ∷ []
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

    forgetμ : {n : ℕ}{t : Tel n}{ty : U (suc n)}{A : Set} 
            → List (Dμ A t ty) → List A
    forgetμ [] = []
    forgetμ (Dμ-A a ∷ ds)      = a ∷ forgetμ ds
    forgetμ (Dμ-dwn _ dx ∷ ds) = forget dx ++ forgetμ ds
    forgetμ (_ ∷ ds)           = forgetμ ds

  -- forget is obviously natural, that is:
  --
  --   forget ∘ D-map f ≡ map f ∘ forget
  --
  -- But since there is no need for this fact, yet,
  -- we leave it unstated.

  {- Some usefull casting operations -}

  cast : {n : ℕ}{t : Tel n}{ty : U n}{A : Set}
       → Patch t ty → D A t ty
  cast = D-map (λ ())

  castμ : {n : ℕ}{t : Tel n}{ty : U (suc n)}{A : Set}
        → Patchμ t ty → List (Dμ A t ty)
  castμ = Dμ-map (λ ())
