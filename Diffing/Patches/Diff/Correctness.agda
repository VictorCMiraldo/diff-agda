open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff

open import Relation.Binary.PropositionalEquality

module Diffing.Patches.Diff.Correctness where
  
  open import Diffing.Utils.Monads
  open Monad {{...}}

  gapply-⊔ : {n : ℕ}{t : Tel n}{ty : U n}{a b : ElU ty t}{d1 d2 : Patch t ty}
           → gapply d1 a ≡ just b
           → gapply d2 a ≡ just b
           → gapply (d1 ⊔ d2) a ≡ just b
  gapply-⊔ {d1 = d1} {d2 = d2} l1 l2 with cost d1 ≤?-ℕ cost d2
  ...| yes prf = l1
  ...| no  prf = l2

  gapplyL-⊔ : {n : ℕ}{t : Tel n}{ty : U (suc n)}{a b : List (ElU (μ ty) t)}
              {d1 d2 : Patchμ t ty}
            → gapplyL d1 a ≡ just b
            → gapplyL d2 a ≡ just b
            → gapplyL (d1 ⊔μ d2) a ≡ just b
  gapplyL-⊔ {d1 = d1} {d2 = d2} l1 l2 with cost (D-mu d1) ≤?-ℕ cost (D-mu d2)
  ...| yes prf = l1
  ...| no  prf = l2

  mutual
    {-# TERMINATING #-}
    correctness : {n : ℕ}{t : Tel n}{ty : U n}(a b : ElU ty t)
                → gapply (gdiff a b) a ≡ just b
    correctness {ty = u1} void void = refl

    correctness {ty = ty ⊕ tv} (inl a) (inl b) 
      rewrite (correctness a b) = refl
    correctness {ty = ty ⊕ tv} (inl a) (inr b) with a ≟-U a
    ...| no a≢a = ⊥-elim (a≢a refl)
    ...| yes _  = refl
    correctness {ty = ty ⊕ tv} (inr a) (inl b) with a ≟-U a
    ...| no a≢a = ⊥-elim (a≢a refl)
    ...| yes _  = refl
    correctness {ty = ty ⊕ tv} (inr a) (inr b) 
      rewrite (correctness a b) = refl

    correctness {ty = ty ⊗ tv} (a1 , a2) (b1 , b2) 
      rewrite (correctness a1 b1)
            | (correctness a2 b2)
            = refl

    correctness {ty = β ty tv} (red a) (red b)
      rewrite (correctness a b) = refl

    correctness {ty = vl} (top a) (top b) 
      rewrite (correctness a b) = refl

    correctness {ty = wk ty} (pop a) (pop b) 
      rewrite (correctness a b) = refl

    correctness {ty = μ ty} (mu da) (mu db)
      rewrite correctnessL (mu da ∷ []) (mu db ∷ []) = refl


    correct-mu-ins-L : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                   → {hdB : ElU ty (tcons u1 t)}
                   → {chB as bs : List (ElU (μ ty) t)}
                   → (b : ElU (μ ty) t)
                   → μ-open b ≡ (hdB , chB)
                   → gapplyL (Dμ-ins hdB ∷ gdiffL as (chB ++ bs)) 
                     as ≡ just (b ∷ bs)
    correct-mu-ins-L {hdB = hdB} {chB = chB} {as = as} {bs = bs} b prf
      rewrite correctnessL as (chB ++ bs)
            | μ-close-resp-arity {l = bs} prf 
            = refl

    correct-mu-down-L : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                   → {hdA hdB : ElU ty (tcons u1 t)}
                   → {chA chB as bs : List (ElU (μ ty) t)}
                   → (a b : ElU (μ ty) t)
                   → μ-open a ≡ (hdA , chA)
                   → μ-open b ≡ (hdB , chB)
                   → gapplyL (Dμ-dwn hdA (D-β (gdiff hdA hdB)) ∷ 
                              gdiffL (chA ++ as) (chB ++ bs)) (a ∷ as)
                   ≡ just (b ∷ bs)
    correct-mu-down-L a b ra rb with μ-open a | μ-open b | inspect μ-open b
    correct-mu-down-L {hdA = hdA} {hdB} {chA} {chB} {as} {bs} a b refl refl
      | .hdA , .chA | .hdB , .chB | [ rb' ]
      with hdA ≟-U hdA
    ...| no absurd = ⊥-elim (absurd refl)
    ...| yes _ 
      rewrite correctness  hdA hdB
            | correctnessL (chA ++ as) (chB ++ bs)
            | μ-close-resp-arity {hdA = hdB} {chA = chB} {l = bs} rb'
            = refl

    correct-mu-del-L : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                   → {hdA : ElU ty (tcons u1 t)}
                   → {chA as bs : List (ElU (μ ty) t)}
                   → (a : ElU (μ ty) t)
                   → μ-open a ≡ (hdA , chA)
                   → gapplyL 
                      (Dμ-del hdA ∷ gdiffL (chA ++ as) bs) (a ∷ as)
                   ≡ just bs
    correct-mu-del-L {hdA = hdA} {chA = chA} {as = as} {bs = bs} a prf
      with correctnessL (chA ++ as) bs | μ-open a
    correct-mu-del-L {hdA = hdA} {chA = chA} {as = as} {bs = bs} 
                     a refl | r | .hdA , .chA 
      with hdA ≟-U hdA
    ...| no absurd = ⊥-elim (absurd refl)
    ...| yes _ rewrite r = refl

    correctnessL : {n : ℕ}{t : Tel n}{ty : U (suc n)}(a b : List (ElU (μ ty) t))
                 → gapplyL (gdiffL a b) a ≡ just b
    correctnessL [] [] = refl
    correctnessL [] (b ∷ bs) with μ-open b | inspect μ-open b
    ...| hdB , chB | [ r ] = correct-mu-ins-L {as = []} {bs = bs} b r
    correctnessL (a ∷ as) [] with μ-open a | inspect μ-open a
    ...| hdA , chA | [ r ] with hdA ≟-U hdA
    ...| no absurd = ⊥-elim (absurd refl)
    ...| yes _     = correctnessL (chA ++ as) []
    correctnessL (a ∷ as) (b ∷ bs) 
      with μ-open a | inspect μ-open a 
    ...| hdA , chA | [ rA ]
      with μ-open b | inspect μ-open b
    ...| hdB , chB | [ rB ] with hdA ≟-U hdB
    ...| no  hdA≢hdB 
       = gapplyL-⊔ 
         {d1 = Dμ-ins hdB ∷ gdiffL (a ∷ as) (chB ++ bs)} 
         (correct-mu-ins-L {as = a ∷ as} {bs = bs} b rB) 
         (gapplyL-⊔ {d1 = Dμ-del hdA ∷ gdiffL (chA ++ as) (b ∷ bs)}
           (correct-mu-del-L {as = as} {bs = b ∷ bs} a rA) 
           (correct-mu-down-L {as = as} {bs = bs} a b rA rB))
    ...| yes hdA≡hdB 
       rewrite rA | rB with hdA ≟-U hdA
    ...| no absurd = ⊥-elim (absurd refl)
    ...| yes _ rewrite correctnessL (chA ++ as) (chB ++ bs)
                     | hdA≡hdB
                     | μ-close-resp-arity {l = bs} rB
                     = refl
