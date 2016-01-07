open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Patches.Diff

open import Relation.Binary.PropositionalEquality

module Diffing.Patches.Metric where

  _-_ : {n : ℕ}{t : Tel n}{ty : U n}
      → ElU ty t → ElU ty t → ℕ
  a - b = cost (gdiff a b)

  dist-comm : {n : ℕ}{t : Tel n}{ty : U n}
            → (a b : ElU ty t)
            → a - b ≡ b - a
  dist-comm a b with gdiff a b | inspect (gdiff a) b
  dist-comm a b | D-A () | _ 
  dist-comm void void | D-void | _ = refl
  dist-comm (inl a₁) (inl b₁) | D-inl p | [ R ] 
    = cong suc {!!}
  dist-comm (inr a₁) (inl b₁) | D-inl p | [ () ]
  dist-comm a₁ (inr b₁) | D-inl p | [ R ] 
    = {!!}
  dist-comm a₁ b₁ | D-inr p | [ R ] 
    = {!!}
  dist-comm a₁ b₁ | D-setl x x₁ | _  = {!!}
  dist-comm a₁ b₁ | D-setr x x₁ | _ = {!!}
  dist-comm (a1 , a2) (b1 , b2) | D-pair p p₁ | [ R ]
    = {!!}
  dist-comm (red a) (red b) | D-β p | _ = {!!}
  dist-comm a₁ b | D-top p | _ = {!!}
  dist-comm a₁ b₁ | D-pop p | _ = {!!}
  dist-comm (mu a) (mu b) | D-mu x | _ = {!!}
  
