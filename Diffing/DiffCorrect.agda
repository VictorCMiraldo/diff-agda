open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Diff

open import Relation.Binary.PropositionalEquality

module Diffing.DiffCorrect where
  
  open import Diffing.Utils.Monads
  open Monad {{...}}

  gapply-⊔ : {n : ℕ}{t : Tel n}{ty : U n}{a b : ElU ty t}{d1 d2 : D t ty}
           → gapply d1 a ≡ just b
           → gapply d2 a ≡ just b
           → gapply (d1 ⊔ d2) a ≡ just b
  gapply-⊔ {d1 = d1} {d2 = d2} l1 l2 with cost d1 ≤?-ℕ cost d2
  ...| yes prf = l1
  ...| no  prf = l2

  gapplyL-⊔ : {n : ℕ}{t : Tel n}{ty : U (suc n)}{a b : List (ElU (μ ty) t)}
              {d1 d2 : D t (μ ty)}
            → gapplyL d1 a ≡ just b
            → gapplyL d2 a ≡ just b
            → gapplyL (d1 ⊔ d2) a ≡ just b
  gapplyL-⊔ {d1 = d1} {d2 = d2} l1 l2 with cost d1 ≤?-ℕ cost d2
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

    correctness {ty = μ ty} a b 
      with μ-open a | inspect μ-open a 
    ...| hdA , chA | [ rA ]
      with μ-open b | inspect μ-open b
    ...| hdB , chB | [ rB ]
      with hdA ≟-U hdB 
    ...| no  hdA≢hdB 
       = gapply-⊔ 
         {d1 = D-mu-ins hdB (gdiffL (a ∷ []) (chB ++ []))}
         (correct-mu-ins a b rB) 
         (gapply-⊔ 
           {d1 = D-mu-del hdA (gdiffL (chA ++ []) (b ∷ []))} 
           (correct-mu-del a b rA)
           (correct-mu-down a b rA rB))
    ...| yes hdA≡hdB 
       rewrite rA | rB
       with hdA ≟-U hdA
    ...| no absurd = ⊥-elim (absurd refl)
    ...| yes _ rewrite correctL (chA ++ []) (chB ++ [])  
                     | hdA≡hdB
                     | μ-close-resp-arity {l = []} rB
       = refl

    correctness {ty = vl} (top a) (top b) 
      rewrite (correctness a b) = refl

    correctness {ty = wk ty} (pop a) (pop b) 
      rewrite (correctness a b) = refl

    correct-mu-ins : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                   → {hdB : ElU ty (tcons u1 t)}
                   → {chB : List (ElU (μ ty) t)}
                   → (a b : ElU (μ ty) t)
                   → μ-open b ≡ (hdB , chB)
                   → gapply (D-mu-ins hdB (gdiffL (a ∷ []) (chB ++ []))) a
                   ≡ just b
    correct-mu-ins {hdB = hdB} {chB = chB} a b prf 
      with correctL (a ∷ []) (chB ++ [])
    ...| r rewrite r with μ-close-resp-arity {l = []} prf 
    ...| s rewrite s = refl

    correct-mu-ins-L : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                   → {hdB : ElU ty (tcons u1 t)}
                   → {chB as bs : List (ElU (μ ty) t)}
                   → (a b : ElU (μ ty) t)
                   → μ-open b ≡ (hdB , chB)
                   → gapplyL (D-mu-ins hdB (gdiffL (a ∷ as) (chB ++ bs))) 
                     (a ∷ as) ≡ just (b ∷ bs)
    correct-mu-ins-L {hdB = hdB} {chB = chB} {as = as} {bs = bs} a b prf
      with correctL (a ∷ as) (chB ++ bs)
    ...| r rewrite r with μ-close-resp-arity {l = bs} prf 
    ...| s rewrite s = refl

    correct-mu-del : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                   → {hdA : ElU ty (tcons u1 t)}
                   → {chA : List (ElU (μ ty) t)}
                   → (a b : ElU (μ ty) t)
                   → μ-open a ≡ (hdA , chA)
                   → gapply (D-mu-del hdA (gdiffL (chA ++ []) (b ∷ []))) a
                   ≡ just b
    correct-mu-del {hdA = hdA} {chA = chA} a b prf
      with correctL (chA ++ []) (b ∷ []) | μ-open a
    correct-mu-del {hdA = hdA} {chA = chA} a b refl | r | .hdA , .chA 
      with hdA ≟-U hdA
    ...| no absurd = ⊥-elim (absurd refl)
    ...| yes _ rewrite r = refl

    correct-mu-del-L : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                   → {hdA : ElU ty (tcons u1 t)}
                   → {chA as bs : List (ElU (μ ty) t)}
                   → (a b : ElU (μ ty) t)
                   → μ-open a ≡ (hdA , chA)
                   → gapplyL 
                      (D-mu-del hdA (gdiffL (chA ++ as) (b ∷ bs))) (a ∷ as)
                   ≡ just (b ∷ bs)
    correct-mu-del-L {hdA = hdA} {chA = chA} {as = as} {bs = bs} a b prf
      with correctL (chA ++ as) (b ∷ bs) | μ-open a
    correct-mu-del-L {hdA = hdA} {chA = chA} {as = as} {bs = bs} 
                     a b refl | r | .hdA , .chA 
      with hdA ≟-U hdA
    ...| no absurd = ⊥-elim (absurd refl)
    ...| yes _ rewrite r = refl

    correct-mu-down : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                   → {hdA hdB : ElU ty (tcons u1 t)}
                   → {chA chB : List (ElU (μ ty) t)}
                   → (a b : ElU (μ ty) t)
                   → μ-open a ≡ (hdA , chA)
                   → μ-open b ≡ (hdB , chB)
                   → gapply (D-mu-down (D-β (gdiff hdA hdB)) 
                            (gdiffL (chA ++ []) (chB ++ []))) a
                   ≡ just b
    correct-mu-down a b ra rb with μ-open a | μ-open b | inspect μ-open b
    correct-mu-down {hdA = hdA} {hdB} {chA} {chB} a b refl refl
      | .hdA , .chA | .hdB , .chB | [ rb' ] 
      rewrite correctness hdA hdB
            | correctL (chA ++ []) (chB ++ [])
      with μ-close-resp-arity {hdA = hdB} {chA = chB} {l = []} rb'
    ...| r rewrite r = refl

    correct-mu-down-L : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                   → {hdA hdB : ElU ty (tcons u1 t)}
                   → {chA chB as bs : List (ElU (μ ty) t)}
                   → (a b : ElU (μ ty) t)
                   → μ-open a ≡ (hdA , chA)
                   → μ-open b ≡ (hdB , chB)
                   → gapplyL (D-mu-down (D-β (gdiff hdA hdB)) 
                            (gdiffL (chA ++ as) (chB ++ bs))) (a ∷ as)
                   ≡ just (b ∷ bs)
    correct-mu-down-L a b ra rb with μ-open a | μ-open b | inspect μ-open b
    correct-mu-down-L {hdA = hdA} {hdB} {chA} {chB} {as} {bs} a b refl refl
      | .hdA , .chA | .hdB , .chB | [ rb' ] 
      rewrite correctness hdA hdB
            | correctL (chA ++ as) (chB ++ bs)
      with μ-close-resp-arity {hdA = hdB} {chA = chB} {l = bs} rb'
    ...| r rewrite r = refl

    correctL : {n : ℕ}{t : Tel n}{ty : U (suc n)}
             → (aL bL : List (ElU (μ ty) t))
             → gapplyL (gdiffL aL bL) aL ≡ just bL
    correctL [] [] = refl
    correctL (a ∷ as) [] with μ-open a | inspect μ-open a
    ...| hdA , chA | [ r ] with hdA ≟-U hdA
    ...| no absurd = ⊥-elim (absurd refl)
    ...| yes _ rewrite correctL (chA ++ as) []
                     = refl
    correctL [] (b ∷ bs) with μ-open b | inspect μ-open b
    ...| hdB , chB | [ r ] 
         rewrite correctL [] (chB ++ bs)
               | μ-close-resp-arity {l = bs} r
               = refl
    correctL (a ∷ as) (b ∷ bs)
      with μ-open b | inspect μ-open b | μ-open a | inspect μ-open a
    ...| hdB , chB | [ rB ] | hdA , chA | [ rA ] with hdA ≟-U hdB
    ...| no  hdA≢hdB 
       = gapplyL-⊔ 
         {d1 = D-mu-ins hdB (gdiffL (a ∷ as) (chB ++ bs))} 
         (correct-mu-ins-L {as = as} {bs = bs} a b rB) 
         (gapplyL-⊔ {d1 = D-mu-del hdA (gdiffL (chA ++ as) (b ∷ bs))} 
           (correct-mu-del-L {as = as} {bs = bs} a b rA) 
           (correct-mu-down-L {as = as} {bs = bs} a b rA rB))
    ...| yes hdA≡hdB rewrite rA with hdA ≟-U hdA
    ...| no  absurd = ⊥-elim (absurd refl)
    ...| yes _ rewrite hdA≡hdB
                     | correctL (chA ++ as) (chB ++ bs)
                     | μ-close-resp-arity {l = bs} rB
             = refl