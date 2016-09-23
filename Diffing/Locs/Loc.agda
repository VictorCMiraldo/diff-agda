open import Prelude hiding (_⊔_)
open import Diffing.Universe
open import CF.Rel.Subtype

module Diffing.Locs.Loc where

  open import Diffing.Patches.D
  open import Diffing.Patches.Cost
  open import Diffing.Diff top-down-cost

  Change : {n : ℕ}(ty : U n)(t : T n)
         → Set
  Change {n} ty t = Σ (Σ ℕ (λ m → U m × T m)) 
                      (λ { (m , (k , t')) → ty [ t ]≥ k [ t' ] × (ElU k t' × ElU k t') })

  on-dir : {n : ℕ}{t : T n}{ty tv : U n}
         → ({m : ℕ}{t' : T m}{k : U m} → ty [ t ]≥ k [ t' ] → tv [ t ]≥ k [ t' ])
         → Change ty t → Change tv t
  on-dir f (k , dir , δ) = k , f dir , δ

  L : {n : ℕ}(ty : U n)(t : T n) → Set
  L ty t = List (Change ty t)

  on-dir* : {n : ℕ}{t : T n}{ty tv : U n}
          → ({m : ℕ}{t' : T m}{k : U m} → ty [ t ]≥ k [ t' ] → tv [ t ]≥ k [ t' ])
          → L ty t → L tv t
  on-dir* f = map (on-dir f)

  change-var : {n : ℕ}{t : T n}{a : U n}
             → Change a t → Change var (a ∷ t)
  change-var (k , dir , δ) = k , (dvar dir , δ)

  change-def : {n : ℕ}{t : T n}{F : U (suc n)}{x : U n}
             → Change F (x ∷ t) → Change (def F x) t
  change-def (k , dir , δ) = k , ddef dir , δ

  change-wk  : {n : ℕ}{t : T n}{a b : U n}
             → Change b t → Change (wk b) (a ∷ t)
  change-wk (k , dir , δ) = k , (dwk dir) , δ

  go : {n : ℕ}{t : T n}{ty : U n}
     → D ⊥ₚ t ty → L ty t
  go (D-A ())
  go D-unit = []
  go (D-inl d) = on-dir* lft (go d)
  go (D-inr d) = on-dir* rgt (go d)
  go {n} {t} {ty ⊕ tv} (D-setl x x₁) = ((n , ty ⊕ tv , t) , here , inl x , inr x₁) ∷ []
  go {n} {t} {ty ⊕ tv} (D-setr x x₁) = ((n , ty ⊕ tv , t) , here , inr x , inl x₁) ∷ []
  go (D-pair d e) 
    = on-dir* fst (go d) ++ on-dir* snd (go e)
  go (D-mu x) = {!!}
  go (D-def d) = map change-def (go d)
  go (D-top d) = map change-var (go d)
  go (D-pop d) = map change-wk (go d)

{--------------------------
   TEST
--------------------------}

  BOOL : {n : ℕ} → U n
  BOOL = u1 ⊕ u1

  F : U 1
  F = BOOL ⊗ var ⊗ var

  e1 e2 : ElU (def F BOOL) []
  e1 = red ((inl unit) , ((top (inl unit)) , (top (inl unit))))
  e2 = red ((inr unit) , (top (inl unit) , top (inr unit)))

  k1 k2 : def F BOOL [ [] ]≥ BOOL [ [] ]
  k1 = ddef (snd (fst (dvar here)))
  k2 = ddef (snd (fst (dvar here)))
  

  k3 : def F BOOL [ [] ]≥ BOOL [ BOOL ∷ [] ]
  k3 = ddef (fst here)

  p12 : D ⊥ₚ [] (def F BOOL) 
  p12 = gdiff e1 e2
