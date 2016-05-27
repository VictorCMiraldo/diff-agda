open import Prelude
open import Diffing.CF-base

open import Diffing.Patches.D

module Diffing.Patches.Diff.Functor where

  {-# TERMINATING #-}
  D-map : {n : ℕ}{t : T n}{ty : U n}
        → {A B : {k : ℕ} → U k → T k → Set}
        → (f : {k : ℕ}{ti : T k}{tyi : U k} → A tyi ti → B tyi ti)
        → D A ty t
        → D B ty t
  D-map f (D-A x) = D-A (f x)
  D-map f (D-μ-A x p) = D-μ-A (f x) (D-map f p)
  D-map f D-unit = D-unit
  D-map f (D-inl d) = D-inl (D-map f d)
  D-map f (D-inr d) = D-inr (D-map f d)
  D-map f (D-setl x x₁) = D-setl x x₁
  D-map f (D-setr x x₁) = D-setr x x₁
  D-map f (D-pair d d₁) = D-pair (D-map f d) (D-map f d₁)
  D-map f (D-μ-dwn d x) = D-μ-dwn (D-map f d) (map (D-map f) x)
  D-map f (D-μ-add x d) = D-μ-add x (D-map f d)
  D-map f (D-μ-rmv x d) = D-μ-rmv x (D-map f d)
  D-map f (D-def d) = D-def (D-map f d)
  D-map f (D-top d) = D-top (D-map f d)
  D-map f (D-pop d) = D-pop (D-map f d)
