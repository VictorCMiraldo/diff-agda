open import Prelude
open import Diffing.Universe
open import Diffing.Patches.D
open import Diffing.Patches.Cost
open import Diffing.Diff
open import Diffing.Apply

module Diffing.Patches.Properties.Correctness where
  
  gdiff-correct
    : {n : ℕ}{t : T n}{ty : U n}{c : Cost}
    → (x y : ElU ty t)
    → gapply (gdiff c x y) x ≡ just y
  gdiff-correct {c = c} x y
    = gapply-spec (gdiff c x y) (gdiff-wf c x y)
