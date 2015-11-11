\begin{code}
open import Prelude
open import Diffing.Universe.Syntax
open import Diffing.Universe.Equality
open import Diffing.Universe.MuUtils
open import Diffing.Patches.Diff
open import Diffing.Patches.DiffCorrect

open import Relation.Binary.PropositionalEquality

module Diffing.Patches.Alignment where
\end{code}

          Alignment
  ============================

  An important notion is the notion of alignment. Two patches
  are said to be aligned if and only if they are defined for the same inputs.

  For instance, Alice and Bob edit a file O, then their patches
  are aligned as applying any of them to O is well-defined.

  The main usefullness of alignment is to be able to perform induction
  on two compatible patches at the same time. For instance,
  for defining a residual patch, we require the two patches to be aligned, as
  it makes no sense to define the residual of two patches that can't be applied
  to the same object.

\begin{code}
  mutual
    data _a⇓_ : {n : ℕ}{t : Tel n}{ty : U n}(x y : D t ty) → Set where
      a-void : {n : ℕ}{t : Tel n} → _a⇓_ {t = t} D-void D-void
      a-id-l : {n : ℕ}{t : Tel n}{ty : U n}{dx : D t ty} → D-id a⇓ dx
      a-id-r : {n : ℕ}{t : Tel n}{ty : U n}{dx : D t ty} → dx   a⇓ D-id
      a-β    : {n : ℕ}{t : Tel n}{a : U n}{ty : U (suc n)}{dx dy : D (tcons a t) ty}
             → dx a⇓ dy → (D-β dx) a⇓ (D-β dy)
      a-top  : {n : ℕ}{t : Tel n}{ty : U n}{dx dy : D t ty}
             → dx a⇓ dy → (D-top dx) a⇓ (D-top dy)
      a-pop  : {n : ℕ}{t : Tel n}{tv : U n}{ty : U n}{dx dy : D t ty}
             → dx a⇓ dy → (D-pop {a = tv} dx) a⇓ (D-pop dy)
      a-pair : {n : ℕ}{t : Tel n}{ty tv : U n}{dx dy : D t ty}{dm dn : D t tv}
             → dx a⇓ dy → dm a⇓ dn → (D-pair dx dm) a⇓ (D-pair dy dn)
      a-inl  : {n : ℕ}{t : Tel n}{ty tv : U n}{dx dy : D t ty}
             → dx a⇓ dy → (D-inl {b = tv} dx) a⇓ (D-inl dy)
      a-inr  : {n : ℕ}{t : Tel n}{ty tv : U n}{dx dy : D t tv}
             → dx a⇓ dy → (D-inr {a = ty} dx) a⇓ (D-inr dy)
      a-setl : {n : ℕ}{t : Tel n}{ty tv : U n}{ea : ElU ty t}{r s : ElU tv t}
             → (D-setl ea r) a⇓ (D-setl ea s)
      a-setinl : {n : ℕ}{t : Tel n}{ty tv : U n}{ea : ElU ty t}{r : ElU tv t}
                 {p : D t ty}
               → (D-setl ea r) a⇓ (D-inl p)
      a-insetl : {n : ℕ}{t : Tel n}{ty tv : U n}{ea : ElU ty t}{r : ElU tv t}
                 {p : D t ty}
               → (D-inl p) a⇓ (D-setl ea r)
      a-setr   : {n : ℕ}{t : Tel n}{ty tv : U n}{ea : ElU tv t}{r s : ElU ty t}
               → (D-setr ea r) a⇓ (D-setr ea s)
      a-setinr : {n : ℕ}{t : Tel n}{ty tv : U n}{ea : ElU ty t}{r : ElU tv t}
                 {p : D t ty}
               → (D-setr ea r) a⇓ (D-inr p)
      a-insetr : {n : ℕ}{t : Tel n}{ty tv : U n}{ea : ElU ty t}{r : ElU tv t}
                 {p : D t ty}
               → (D-inr p) a⇓ (D-setr ea r)
      a-mu : {n : ℕ}{t : Tel n}{ty : U (suc n)}{da db : List (Dμ t ty)}
           → da a⇓* db → (D-mu da) a⇓ (D-mu db)
      

    data _a⇓*_ : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                (x y : List (Dμ t ty)) → Set where
      -- empty edits are aligned.
      a*-nil   : {n : ℕ}{t : Tel n}{ty : U (suc n)} → _a⇓*_ {t = t} {ty = ty} [] []

      -- fixpoints can grow freely, if needed.
      a*-ins-l : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
                 {el : ValU ty t}
               → d1 a⇓* d2 → (Dμ-ins el ∷ d1) a⇓* d2
      a*-ins-r : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
                 {el : ValU ty t}
               → d1 a⇓* d2 → d1 a⇓* (Dμ-ins el ∷ d2)

      -- Structural changes are aligned iff the changes itself are aligned.
      a*-dwn   : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
                 {dx dy : D t (β ty u1)}
               → dx a⇓ dy → d1 a⇓* d2 → (Dμ-dwn dx ∷ d1) a⇓* (Dμ-dwn dy ∷ d2)
    
      a*-deldel : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
                  {el : ValU ty t}
                → d1 a⇓* d2 → (Dμ-del el ∷ d1) a⇓* (Dμ-del el ∷ d2)
      a*-delcpy : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
                  {el : ValU ty t}
                → d1 a⇓* d2 → (Dμ-del el ∷ d1) a⇓* (Dμ-cpy el ∷ d2)
      a*-cpydel : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
                  {el : ValU ty t}
                → d1 a⇓* d2 → (Dμ-cpy el ∷ d1) a⇓* (Dμ-del el ∷ d2)
      a*-cpycpy : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
                  {el : ValU ty t}
                → d1 a⇓* d2 → (Dμ-cpy el ∷ d1) a⇓* (Dμ-cpy el ∷ d2)
      a*-dwncpy : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
                  {dx : D t (β ty u1)}{el k : ValU ty t}
                → gapply dx (red el) ≡ just (red k)
                → d1 a⇓* d2 → (Dμ-dwn dx ∷ d1) a⇓* (Dμ-cpy el ∷ d2)
      a*-cpydwn : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
                  {dx : D t (β ty u1)}{el k : ValU ty t}
                → gapply dx (red el) ≡ just (red k)
                → d1 a⇓* d2 → (Dμ-cpy el ∷ d1) a⇓* (Dμ-dwn dx ∷ d2)
      a*-dwndel : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
                  {dx : D t (β ty u1)}{el k : ValU ty t}
                → gapply dx (red el) ≡ just (red k)
                → d1 a⇓* d2 → (Dμ-dwn dx ∷ d1) a⇓* (Dμ-del el ∷ d2)
      a*-deldwn : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
                  {dx : D t (β ty u1)}{el k : ValU ty t}
                → gapply dx (red el) ≡ just (red k)
                → d1 a⇓* d2 → (Dμ-del el ∷ d1) a⇓* (Dμ-dwn dx ∷ d2)
\end{code}

  Now we can prove a few alignment properties.

\begin{code}
  mutual
\end{code}
%<*align-sym-type>
\begin{code}
    align-sym : {n : ℕ}{t : Tel n}{ty : U n}{d1 d2 : D t ty}
              → d1 a⇓ d2 → d2 a⇓ d1
\end{code}
%</align-sym-type>
\begin{code}
    align-sym a-void = a-void
    align-sym a-id-l = a-id-r
    align-sym a-id-r = a-id-l
    align-sym (a-β a₁) = a-β (align-sym a₁)
    align-sym (a-top a₁) = a-top (align-sym a₁)
    align-sym (a-pop a) = a-pop (align-sym a)
    align-sym (a-pair a a₁) = a-pair (align-sym a) (align-sym a₁)
    align-sym (a-inl a) = a-inl (align-sym a)
    align-sym (a-inr a) = a-inr (align-sym a)
    align-sym a-setl = a-setl
    align-sym a-setinl = a-insetl
    align-sym a-insetl = a-setinl
    align-sym a-setr = a-setr
    align-sym a-setinr = a-insetr
    align-sym a-insetr = a-setinr
    align-sym (a-mu x) = a-mu (alignL-sym x)
 
    alignL-sym : {n : ℕ}{t : Tel n}{ty : U (suc n)}{d1 d2 : List (Dμ t ty)}
               → d1 a⇓* d2 → d2 a⇓* d1
    alignL-sym = {!!}

\end{code}

  Intuition tells me this is going to be reflexive and transitive too...
  Yet, these proofs will be left for later. Let's prove that this
  is, in fact, capturing the notion we're looking for!



\begin{code}
  align-correct : {n : ℕ}{t : Tel n}{ty : U n}
                  (d1 d2 : D t ty)(x : ElU ty t)
                → IsJust (gapply d1 x)
                → IsJust (gapply d2 x)
                → d1 a⇓ d2
  align-correct D-void D-void x p1 p2 = a-void
  align-correct _ D-id x p1 p2 = a-id-r
  align-correct D-id _ x p1 p2 = a-id-l
  align-correct (D-inl d1) (D-inl d2) (inl x) p1 p2 = a-inl (align-correct d1 d2 x {!p1!} {!!})
  align-correct (D-inl d1) (D-inl d2) (inr x) p1 p2 = {!!}
  align-correct (D-inl d1) (D-inr d2) x p1 p2 = {!!}
  align-correct (D-inl d1) (D-setl x x₁) x₂ p1 p2 = {!!}
  align-correct (D-inl d1) (D-setr x x₁) x₂ p1 p2 = {!!}
  align-correct (D-inr d1) d2 x p1 p2 = {!!}
  align-correct (D-setl x x₁) d2 x₂ p1 p2 = {!!}
  align-correct (D-setr x x₁) d2 x₂ p1 p2 = {!!}
  align-correct (D-pair d1 d2) d3 x p1 p2 = {!!}
  align-correct (D-β d1) d2 x₁ p1 p2 = {!!}
  align-correct (D-top d1) d2 x p1 p2 = {!!}
  align-correct (D-pop d1) d2 x p1 p2 = {!!}
  align-correct (D-mu d1) (D-mu d2) (mu x) p1 p2 = a-mu {!!}
    where
      align*-correct : {n : ℕ}{t : Tel n}{ty : U (suc n)}
                      (d1 d2 : List (Dμ t ty))(x : List (ElU (μ ty) t))
                    → IsJust (gapplyL d1 x)
                    → IsJust (gapplyL d2 x)
                    → d1 a⇓* d2
      align*-correct [] [] [] p3 p4 = a*-nil
      align*-correct [] [] (x₁ ∷ x₂) p3 p4 = a*-nil
      align*-correct [] (Dμ-ins x₁ ∷ d3) [] p3 p4 = a*-ins-r (align*-correct [] d3 [] unit {!!})
      align*-correct [] (Dμ-del x₁ ∷ d3) [] p3 ()
      align*-correct [] (Dμ-cpy x₁ ∷ d3) [] p3 ()
      align*-correct [] (Dμ-dwn x₁ ∷ d3) [] p3 ()
      align*-correct [] (Dμ-ins x₁ ∷ d3) (x₂ ∷ x₃) p3 p4 
        = a*-ins-r (align*-correct [] d3 (x₂ ∷ x₃) unit {!!})
      align*-correct [] (Dμ-del x₁ ∷ d3) (x₂ ∷ x₃) p3 p4 = {!!}
      align*-correct [] (Dμ-cpy x₁ ∷ d3) (x₂ ∷ x₃) p3 p4 = {!!}
      align*-correct [] (Dμ-dwn x₁ ∷ d3) (x₂ ∷ x₃) p3 p4 = {!!}
      align*-correct (x₁ ∷ d3) [] [] p3 p4 = {!!}
      align*-correct (x₁ ∷ d3) [] (x₂ ∷ x₃) p3 p4 = {!!}
      align*-correct (x₁ ∷ d3) (x₂ ∷ d4) [] p3 p4 = {!!}
      align*-correct (x₁ ∷ d3) (x₂ ∷ d4) (x₃ ∷ x₄) p3 p4 = {!!}
\end{code}

%<*align-correct-type>
begin{code}
  {-# TERMINATING #-}
  align-correct : {n : ℕ}{t : Tel n}{ty : U n}(eO eA eB : ElU ty t)
                → (gdiff eO eA) a⇓ (gdiff eO eB)
end{code}
%</align-correct-type>
begin{code}
  align-correct void void void = a-void

  align-correct (inl eO) (inl eA) (inl eB) = a-inl (align-correct eO eA eB)
  align-correct (inl eO) (inl eA) (inr eB) = a-insetl
  align-correct (inl eO) (inr eA) (inl eB) = a-setinl
  align-correct (inl eO) (inr eA) (inr eB) = a-setl
  align-correct (inr eO) (inl eA) (inl eB) = a-setr
  align-correct (inr eO) (inl eA) (inr eB) = a-setinr
  align-correct (inr eO) (inr eA) (inl eB) = a-insetr
  align-correct (inr eO) (inr eA) (inr eB) = a-inr (align-correct eO eA eB)

  align-correct (eO , eO₁) (eA , eA₁) (eB , eB₁) 
    = a-pair (align-correct eO eA eB) (align-correct eO₁ eA₁ eB₁)

  align-correct (top eO) (top eA) (top eB) = a-top (align-correct eO eA eB)
  align-correct (pop eO) (pop eA) (pop eB) = a-pop (align-correct eO eA eB)
  align-correct (red eO) (red eA) (red eB) = a-β (align-correct eO eA eB)
  align-correct (mu eO) (mu eA) (mu eB) 
    = a-mu (align*-correct (mu eO ∷ []) (mu eA ∷ []) (mu eB ∷ []))
    where
      _a⊔*_ : {n : ℕ}{t : Tel n}{ty : U (suc n)}{da db dc : List (Dμ t ty)}
                 → da a⇓* db → da a⇓* dc → da a⇓* (db ⊔μ dc)
      _a⊔*_ {db = db} {dc = dc} dadb dadc with cost (D-mu db) ≤?-ℕ cost (D-mu dc)
      ...| yes _ = dadb
      ...| no  _ = dadc

      mutual
        
        align*-del : {n : ℕ}{t : Tel n}{ty : U (suc n)}(o : ElU (μ ty) t)(hdO : ValU ty t)
                      (chO as bs os : List (ElU (μ ty) t))
                    → μ-open o ≡ (hdO , chO)
                    → gdiffL (o ∷ os) as a⇓* (Dμ-del hdO ∷ gdiffL (chO ++ os) bs)
        align*-del o hdO chO [] bs os prf with μ-open o
        align*-del o hdO chO [] bs os refl | .hdO , .chO = a*-deldel (align*-correct (chO ++ os) [] bs)
        align*-del o hdO chO (a ∷ as) bs os prf with μ-open o
        align*-del o hdO chO (a ∷ as) bs os refl | .hdO , .chO with μ-open a
        ...| hdA , chA with hdO ≟-U hdA
        ...| yes o≡a = a*-cpydel (align*-correct (chO ++ os) (chA ++ as) bs)
        ...| no  o≢a = alignL-sym (_a⊔*_ {db = Dμ-ins hdA ∷ gdiffL (o ∷ os) (chA ++ as)} 
                                         {!!} 
                                  (_a⊔*_ {db = Dμ-del hdO ∷ gdiffL (chO ++ os) (a ∷ as)} 
                                         {!!} 
                                         {!!}))
        
        align*-cpy : {n : ℕ}{t : Tel n}{ty : U (suc n)}(o : ElU (μ ty) t)(hdO : ValU ty t)
                      (chO as bs os : List (ElU (μ ty) t))
                    → μ-open o ≡ (hdO , chO)
                    → gdiffL (o ∷ os) as a⇓* (Dμ-cpy hdO ∷ gdiffL (chO ++ os) bs)
        align*-cpy o hdO chO [] bs os prf with μ-open o
        align*-cpy o hdO chO [] bs os refl | .hdO , .chO 
          = a*-delcpy (align*-correct (chO ++ os) [] bs)
        align*-cpy o hdO chO (a ∷ as) bs os prf with μ-open o | inspect μ-open o
        align*-cpy o hdO chO (a ∷ as) bs os refl | .hdO , .chO | [ rO ] with μ-open a
        ...| hdA , chA with hdO ≟-U hdA
        ...| yes o≡a = a*-cpycpy (align*-correct (chO ++ os) (chA ++ as) bs)
        ...| no  o≢a = alignL-sym (_a⊔*_ {db = Dμ-ins hdA ∷ gdiffL (o ∷ os) (chA ++ as)} 
                                  (a*-ins-r (alignL-sym (align*-cpy o hdO chO (chA ++ as) bs os rO))) 
                                  (_a⊔*_ {db = Dμ-del hdO ∷ gdiffL (chO ++ os) (a ∷ as)} 
                                  (a*-cpydel (align*-correct (chO ++ os) bs (a ∷ as))) 
                                  (a*-cpydwn (correctness (red hdO) (red hdA)) 
                                             (align*-correct (chO ++ os) bs (chA ++ as)))))

        align*-dwn : {n : ℕ}{t : Tel n}{ty : U (suc n)}(o : ElU (μ ty) t)
                     (hdO : ValU ty t){el : ValU ty t}
                     (chO as bs os : List (ElU (μ ty) t))(dx : D t (β ty u1))
                    → μ-open o ≡ (hdO , chO)
                    → gapply dx (red hdO) ≡ just (red el)
                    → gdiffL (o ∷ os) as a⇓* (Dμ-dwn dx ∷ gdiffL (chO ++ os) bs)
        align*-dwn o hdO chO [] bs os dx prf app with μ-open o
        align*-dwn o hdO chO [] bs os dx refl app | .hdO , .chO 
          = a*-deldwn app (align*-correct (chO ++ os) [] bs)
        align*-dwn o hdO chO (a ∷ as) bs os dx prf app with μ-open o | inspect μ-open o
        align*-dwn o hdO chO (a ∷ as) bs os dx refl app | .hdO , .chO | [ rO ] with μ-open a
        ...| hdA , chA with hdO ≟-U hdA
        ...| yes o≡a = a*-cpydwn app (align*-correct (chO ++ os) (chA ++ as) bs)
        ...| no  o≢a = alignL-sym (_a⊔*_ {db = Dμ-ins hdA ∷ gdiffL (o ∷ os) (chA ++ as)} 
                                  (a*-ins-r (alignL-sym (align*-dwn o hdO chO (chA ++ as) bs os dx rO app))) 
                                  (_a⊔*_ {db = Dμ-del hdO ∷ gdiffL (chO ++ os) (a ∷ as)} 
                                  (a*-dwndel app (align*-correct (chO ++ os) bs (a ∷ as))) 
                                  (a*-dwn {!!} (align*-correct (chO ++ os) bs (chA ++ as)))))

        {-# TERMINATING #-}
        align*-correct : {n : ℕ}{t : Tel n}{ty : U (suc n)}(eO eA eB : List (ElU (μ ty) t))
                       → (gdiffL eO eA) a⇓* (gdiffL eO eB)
        align*-correct [] [] [] = a*-nil
        align*-correct [] [] (b ∷ bs) with μ-open b
        ...| hdB , chB = a*-ins-r (align*-correct [] [] (chB ++ bs))
        align*-correct [] (a ∷ as) [] with μ-open a
        ...| hdA , chA = a*-ins-l (align*-correct [] (chA ++ as) [])
        align*-correct [] (a ∷ as) (b ∷ bs) with μ-open a | μ-open b
        ...| hdA , chA | hdB , chB = a*-ins-l (a*-ins-r (align*-correct [] (chA ++ as) (chB ++ bs)))
        align*-correct (o ∷ os) [] [] with μ-open o
        ...| hdO , chO = a*-deldel (align*-correct (chO ++ os) [] [])
        align*-correct (o ∷ os) [] (b ∷ bs) with μ-open o | inspect μ-open o | μ-open b
        ...| hdO , chO | [ rO ] | hdB , chB with hdO ≟-U hdB
        ...| yes o≡b = a*-delcpy (align*-correct (chO ++ os) [] (chB ++ bs))
        ...| no  o≢b = _a⊔*_ {db = Dμ-ins hdB ∷ gdiffL (o ∷ os) (chB ++ bs)} 
                     (a*-ins-r (alignL-sym (align*-del o hdO chO (chB ++ bs) [] os rO)))
                     (_a⊔*_ {db = Dμ-del hdO ∷ gdiffL (chO ++ os) (b ∷ bs)} 
                     (a*-deldel (align*-correct (chO ++ os) [] (b ∷ bs))) 
                     (a*-deldwn (correctness (red hdO) (red hdB)) (align*-correct (chO ++ os) [] (chB ++ bs))))
        align*-correct (o ∷ os) (a ∷ as) [] with μ-open o | inspect μ-open o | μ-open a
        ...| hdO , chO | [ rO ] | hdA , chA with hdO ≟-U hdA
        ...| yes o≡a = a*-cpydel (align*-correct (chO ++ os) (chA ++ as) [])
        ...| no  o≢a = alignL-sym (_a⊔*_ {db = Dμ-ins hdA ∷ gdiffL (o ∷ os) (chA ++ as)} 
                                   (a*-ins-r (alignL-sym (align*-del o hdO chO (chA ++ as) [] os rO))) 
                                   (_a⊔*_ {db = Dμ-del hdO ∷ gdiffL (chO ++ os) (a ∷ as)} 
                                   (a*-deldel (align*-correct (chO ++ os) [] (a ∷ as))) 
                                   (a*-deldwn (correctness (red hdO) (red hdA)) 
                                              (align*-correct (chO ++ os) [] (chA ++ as)))))
        align*-correct (o ∷ os) (a ∷ as) (b ∷ bs) 
          with μ-open o | inspect μ-open o | μ-open a |  μ-open b
        ...| hdO , chO | [ rO ] | hdA , chA | hdB , chB
          with hdO ≟-U hdA | hdO ≟-U hdB
        ...| yes o≡a | yes o≡b = a*-cpycpy (align*-correct (chO ++ os) (chA ++ as) (chB ++ bs))
        ...| yes o≡a | no  o≢b
           = _a⊔*_ {db = Dμ-ins hdB ∷ gdiffL (o ∷ os) (chB ++ bs)} 
                   (a*-ins-r (alignL-sym (align*-cpy o hdO chO (chB ++ bs) (chA ++ as) os rO)))
                   (_a⊔*_ {db = Dμ-del hdO ∷ gdiffL (chO ++ os) (b ∷ bs)} 
                   (a*-cpydel (align*-correct (chO ++ os) (chA ++ as) (b ∷ bs))) 
                   (a*-cpydwn (correctness (red hdO) (red hdB)) 
                              (align*-correct (chO ++ os) (chA ++ as) (chB ++ bs))))
        ...| no  o≢a | yes o≡b = alignL-sym
           (_a⊔*_ {db = Dμ-ins hdA ∷ gdiffL (o ∷ os) (chA ++ as)} 
                   (a*-ins-r (alignL-sym (align*-cpy o hdO chO (chA ++ as) (chB ++ bs) os rO)))
                   (_a⊔*_ {db = Dμ-del hdO ∷ gdiffL (chO ++ os) (a ∷ as)} 
                   (a*-cpydel (align*-correct (chO ++ os) (chB ++ bs) (a ∷ as))) 
                   (a*-cpydwn (correctness (red hdO) (red hdA)) 
                              (align*-correct (chO ++ os) (chB ++ bs) (chA ++ as)))))
        ...| no  o≢a | no  o≢b
           = _a⊔*_ {db = Dμ-ins hdB ∷ gdiffL (o ∷ os) (chB ++ bs)} 
                   (alignL-sym 
                     (_a⊔*_ {db = Dμ-ins hdA ∷ gdiffL (o ∷ os) (chA ++ as)} 
                      (a*-ins-l (a*-ins-r (align*-correct (o ∷ os) (chB ++ bs) (chA ++ as))))
                      (_a⊔*_ {db = Dμ-del hdO ∷ gdiffL (chO ++ os) (a ∷ as)} 
                      (a*-ins-l (align*-del o hdO chO (chB ++ bs) (a ∷ as) os rO)) 
                      (a*-ins-l (align*-dwn o hdO chO (chB ++ bs) (chA ++ as) os
                                   (D-β (gdiff hdO hdA)) rO (correctness (red hdO) (red hdA))))))
                   )
                   (_a⊔*_ {db = Dμ-del hdO ∷ gdiffL (chO ++ os) (b ∷ bs)} 
                   (alignL-sym
                     (_a⊔*_ {db = Dμ-ins hdA ∷ gdiffL (o ∷ os) (chA ++ as)} 
                      (a*-ins-r (alignL-sym (align*-del o hdO chO (chA ++ as) (b ∷ bs) os rO)))
                      (_a⊔*_ {db = Dμ-del hdO ∷ gdiffL (chO ++ os) (a ∷ as)} 
                      (a*-deldel (align*-correct (chO ++ os) (b ∷ bs) (a ∷ as))) 
                      (a*-deldwn (correctness (red hdO) (red hdA)) 
                                 (align*-correct (chO ++ os) (b ∷ bs) (chA ++ as)))))
                   ) 
                   (alignL-sym
                     (_a⊔*_ {db = Dμ-ins hdA ∷ gdiffL (o ∷ os) (chA ++ as)} 
                      (a*-ins-r (alignL-sym (align*-dwn o hdO chO (chA ++ as) (chB ++ bs) os 
                                             (D-β (gdiff hdO hdB)) rO (correctness (red hdO) (red hdB)))))
                      (_a⊔*_ {db = Dμ-del hdO ∷ gdiffL (chO ++ os) (a ∷ as)} 
                      (a*-dwndel (correctness (red hdO) (red hdB)) 
                                 (align*-correct (chO ++ os) (chB ++ bs) (a ∷ as))) 
                      (a*-dwn (align-correct (red hdO) (red hdB) (red hdA)) 
                              (align*-correct (chO ++ os) (chB ++ bs) (chA ++ as)))))
                   )) 
end{code}
