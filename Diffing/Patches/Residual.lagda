\begin{code}
open import Prelude
open import Prelude.ListProperties using (All; all?; ∷-inj)
open import Prelude.Monad
open import Diffing.CF-base
open import CF.Operations.Derivative

open import Diffing.Patches.D
open import Diffing.Patches.Diff.Functor
open import Diffing.Patches.Conflicts

module Diffing.Patches.Residual where

  open Monad {{...}}
\end{code}

\begin{code}
  select : {A : Set} → ℕ → List A → Maybe A
  select n [] = nothing
  select zero    (x ∷ as) = just x
  select (suc n) (x ∷ as) = select n as
\end{code}

\begin{code}
  {-# TERMINATING #-}
  res : {n : ℕ}{t : T n}{ty : U n}
      → (p q : Patch ty t)
      → Maybe (D C ty t)
  res (D-A ()) q
  res (D-μ-A () _) _
  res p (D-A ())
  res _ (D-μ-A () _)
  res D-unit D-unit = just D-unit
  
  res (D-inl p) (D-inl q) = D-inl <M> res p q
  res (D-inl p) (D-setl x y)
    with D-is-id? p
  ...| yes _ = just (D-setl x y)
  ...| no  _ = (D-A ∘ (λ z → UU (inl x) (inl z) (inr y))) <M> D-dst p
  res (D-inr p) (D-inr q) = D-inr <M> res p q
  res (D-inr p) (D-setr x y)
    with D-is-id? p
  ...| yes _ = just (D-setr x y)
  ...| no  _ = (D-A ∘ (λ z → UU (inr x) (inr z) (inl y))) <M> D-dst p
  res (D-setl x y) (D-setl w z)
    with x ≟-U w | y ≟-U z
  ...| yes xw | yes yz = just (gdiff-id (inr z))
  ...| no _   | _      = nothing
  ...| yes xw | no ¬yz = just (D-A (UU (inl x) (inr y) (inr z)))
  res (D-setr x y) (D-inr q)
    with D-is-id? q
  ...| yes _ = just (D-setr x y)
  ...| no  _ = (D-A ∘ (λ z → UU (inr x) (inl y) (inr z))) <M> D-dst q
  res (D-setr x y) (D-setr w z)
    with x ≟-U w | y ≟-U z
  ...| yes xw | yes yz = just (gdiff-id (inl z))
  ...| no _   | _      = nothing
  ...| yes xw | no ¬yz = just (D-A (UU (inr x) (inl y) (inl z)))
  res (D-setl x y) (D-inl q)
    with D-is-id? q
  ...| yes _ = just (D-setl x y)
  ...| no  _ = (D-A ∘ (λ z → UU (inl x) (inr y) (inl z))) <M> D-dst q
  res (D-inr p) (D-inl q) = nothing
  res (D-inl p) (D-inr q) = nothing
  res (D-inl p) (D-setr x x₁) = nothing
  res (D-inr p) (D-setl x x₁) = nothing
  res (D-setl x x₁) (D-inr q) = nothing
  res (D-setl x x₁) (D-setr x₂ x₃) = nothing
  res (D-setr x x₁) (D-inl q) = nothing
  res (D-setr x x₁) (D-setl x₂ x₃) = nothing
  
  res (D-pair p p₁) (D-pair q q₁)
    = D-pair <M> res p q <M*> res p₁ q₁
  
  res (D-def p) (D-def q) = D-def <M> res p q
  res (D-top p) (D-top q) = D-top <M> res p q
  res (D-pop p) (D-pop q) = D-pop <M> res p q

  res (D-μ-add ctx p) (D-μ-add dtx q)
    = D-μ-A (GLR ctx dtx) <M> res p q
  res (D-μ-add ctx p) q
    = D-μ-A (GL ctx) <M> res p q
  res p (D-μ-add ctx q)
    = D-μ-A (GR ctx) <M> res p q
    
  -- assumes length ps ≡ length qs ≡ ar (D-src p) ≡ ar (D-dst q) ≡ ..
  res (D-μ-dwn p ps) (D-μ-dwn q qs)
    = D-μ-dwn <M> res p q <M*> zipWithM res ps qs

  -- Assumes length ps ≡ suc (φ-ar 0 ctx)
  res (D-μ-dwn p ps) (D-μ-rmv ctx q)
    with D-dst (D-μ-dwn p ps)
  ...| nothing = nothing
  ...| just (mu x) with match ctx x
  ...| nothing = D-μ-A (UD ctx (mu x)) <M> (select (Zidx ctx) ps >>= flip res q)
  ...| just x' = select (Zidx ctx) ps >>= flip res q


  res (D-μ-rmv ctx p) (D-μ-dwn q qs)
    with D-dst (D-μ-dwn q qs)
  ...| nothing = nothing
  ...| just (mu x) with match ctx x
  ...| nothing = D-μ-A (DU ctx (mu x)) <M> (select (Zidx ctx) qs >>= res p)
  ...| just x' = D-μ-rmv ctx <M> (select (Zidx ctx) qs >>= res p)
  
  res (D-μ-rmv ctx p) (D-μ-rmv dtx q)
    with ctx ≟-Ctx dtx
  ...| yes pq = res p q
  ...| no ¬pq = D-μ-A (DD ctx dtx) <M> res p q
\end{code}

\begin{code}
  {-# TERMINATING #-}
  res-symmetric
    : {n : ℕ}{t : T n}{ty : U n}
    → (p q : Patch ty t)(pq : D C ty t)
    → res p q ≡ just pq
    → Σ ({A : {k : ℕ} → U k → T k → Set} → D A ty t → D A ty t)
        (λ f → res q p ≡ just (D-map C-sym (f pq)))

  res-symmetric-zipwith
    : {n : ℕ}{t : T n}{ty : U n}
    → (ps qs : List (Patch ty t))
    → (as    : List (D C ty t))
    → zipWithM res ps qs ≡ just as
    → Σ (List ({A : {k : ℕ} → U k → T k → Set} → D A ty t → D A ty t))
        (λ f → zipWithM res qs ps ≡ just (map (D-map C-sym) (zipWith (λ f x → f x) f as)))
  res-symmetric-zipwith [] [] .[] refl = [] , refl
  res-symmetric-zipwith [] (x ∷ qs) .[] refl = [] , refl
  res-symmetric-zipwith (x ∷ ps) [] .[] refl = [] , refl
  res-symmetric-zipwith (p ∷ ps) (q ∷ qs) [] hip
    with res p q
  ...| nothing = ⊥-elim (Maybe-⊥ (sym hip))
  ...| just pq with zipWithM res ps qs
  ...| nothing  = ⊥-elim (Maybe-⊥ (sym hip))
  res-symmetric-zipwith (p ∷ ps) (q ∷ qs) [] ()
     | just pq | just pqs 
  res-symmetric-zipwith (p ∷ ps) (q ∷ qs) (a ∷ as) hip
    with res p q | inspect (res p) q
  ...| nothing | _ = ⊥-elim (Maybe-⊥ (sym hip))
  ...| just pq | [ R0 ] with zipWithM res ps qs | inspect (zipWithM res ps) qs
  ...| nothing  | _     = ⊥-elim (Maybe-⊥ (sym hip))
  ...| just pqs | [ R1 ] with res-symmetric-zipwith ps qs pqs R1
  ...| ks , res with res-symmetric p q pq R0
  res-symmetric-zipwith (p ∷ ps) (q ∷ qs) (a ∷ as) hip
     | just pq | [ R0 ] | just pqs | [ R1 ] | ks , res
     | f , res0 rewrite res0 | res
                 | p1 (∷-inj (just-inj hip))
                 | p2 (∷-inj (just-inj hip))
     = f ∷ ks , refl

\end{code}
\begin{code}
  res-symmetric (D-A ()) q pq hip
  res-symmetric p (D-A ()) pq hip
  res-symmetric p (D-μ-A () _) pq hip
  res-symmetric (D-μ-A () _) q pq hip
  res-symmetric D-unit D-unit (D-A ()) hip
  res-symmetric D-unit D-unit D-unit hip = id , refl
  
  res-symmetric (D-inl p) (D-inl q) pq hip
    with <M>-elim hip
  ...| r , s , t with res-symmetric p q r t
  res-symmetric (D-inl p) (D-inl q) .(D-inl r) hip
     | r , refl , t | f , res
     = (λ { (D-inl z) → D-inl (f z); z → z })
     , cong (_<M>_ D-inl) res
     
  res-symmetric (D-inl p) (D-inr q) pq ()
  
  res-symmetric (D-inl p) (D-setl x x₁) pq hip
    with D-is-id? p
  ...| no ¬idp with <M>-elim hip
  ...| m , n , o rewrite o | n
     = id , refl
  res-symmetric (D-inl p) (D-setl x x₁) .(D-setl x x₁) refl
     | yes idp = id , refl
     
  res-symmetric (D-inl p) (D-setr x x₁) pq ()

  res-symmetric (D-inr p) (D-inl q) pq ()
  
  res-symmetric (D-inr p) (D-inr q) pq hip
    with <M>-elim hip
  ...| r , s , t with res-symmetric p q r t
  res-symmetric (D-inr p) (D-inr q) .(D-inr r) hip
     | r , refl , t | f , res
     = (λ { (D-inr z) → D-inr (f z); z → z })
     , cong (_<M>_ D-inr) res
  res-symmetric (D-inr p) (D-setl x x₁) pq ()
  
  res-symmetric (D-inr p) (D-setr x x₁) pq hip
    with D-is-id? p
  ...| no ¬idp with <M>-elim hip
  ...| m , n , o rewrite o | n
     = id , refl
  res-symmetric (D-inr p) (D-setr x x₁) .(D-setr x x₁) refl
     | yes idp = id , refl

  res-symmetric (D-setl x x₁) (D-inl q) pq hip
    with D-is-id? q
  res-symmetric (D-setl x x₁) (D-inl q) .(D-setl x x₁) refl
     | yes idq = id , refl
  ...| no _    with <M>-elim hip
  ...| m , n , o rewrite o | n
     = id , refl
  res-symmetric (D-setl x x₁) (D-inr q) pq ()
  res-symmetric (D-setl x x₁) (D-setl x₂ x₃) pq hip
    with x₂ ≟-U x | x ≟-U x₂
  ...| yes a | no  b = ⊥-elim (Maybe-⊥ (sym hip))
  ...| no  a | yes b = ⊥-elim (a (sym b))
  ...| no  a | no  b = ⊥-elim (Maybe-⊥ (sym hip))
  ...| yes a | yes b with x₁ ≟-U x₃ | x₃ ≟-U x₁
  ...| yes c | no  d = ⊥-elim (d (sym c))
  ...| no  c | yes d = ⊥-elim (c (sym d))
  res-symmetric (D-setl x x₁) (D-setl x₂ x₃) .(D-inr (gdiff-id x₃)) refl
     | yes a | yes b | yes c | yes d
     rewrite c = id , {!!}
  ...| no  c | no  d 
     rewrite just-inj (sym hip) | a
       = id , refl
  
  res-symmetric (D-setl x x₁) (D-setr x₂ x₃) pq hip = {!!}

  res-symmetric (D-setr x x₁) (D-inl q) pq hip = {!!}
  res-symmetric (D-setr x x₁) (D-inr q) pq hip = {!!}
  res-symmetric (D-setr x x₁) (D-setl x₂ x₃) pq hip = {!!}
  res-symmetric (D-setr x x₁) (D-setr x₂ x₃) pq hip = {!!}

  res-symmetric (D-pair p p₁) (D-pair q q₁) pq hip = {!!}

  res-symmetric (D-def p) (D-def q) pq hip = {!!}

  res-symmetric (D-top p) (D-top q) pq hip = {!!}
 
  res-symmetric (D-pop p) (D-pop q) pq hip = {!!}

  res-symmetric (D-μ-add x p) (D-μ-add x₁ q) pq hip = {!!}
  res-symmetric (D-μ-dwn p x) (D-μ-add x₁ q) pq hip = {!!}
  res-symmetric (D-μ-rmv x p) (D-μ-add x₁ q) pq hip = {!!}
  res-symmetric (D-μ-add x p) (D-μ-dwn q x₁) pq hip = {!!}
  res-symmetric (D-μ-add x p) (D-μ-rmv x₁ q) pq hip = {!!}

  
  res-symmetric {t = t} {ty = μ ty} (D-μ-dwn p x) (D-μ-dwn q x₁) pq hip
    with <M*>-elim-full {A = List (D C (μ ty) t)}
         {f = D-μ-dwn <M> res p q} {x = zipWithM res x x₁}  hip
  ...| (f , a) , (q0 , q1 , q2) with <M>-elim q0
  ...| m , n , o with res-symmetric p q m o
  ...| g , res rewrite res | n | q1 with res-symmetric-zipwith x x₁ a q2
  ...| ks , rs rewrite rs
    = (λ { (D-μ-dwn x xs) → D-μ-dwn (g x) (zipWith (λ f x → f x) ks xs) ; x → x})
    , refl
  
  res-symmetric (D-μ-dwn p x) (D-μ-rmv x₁ q) pq hip
    with D-dst (D-μ-dwn p x)
  ...| nothing = ⊥-elim (Maybe-⊥ (sym hip))
  ...| just (mu x') with match x₁ x'
  ...| nothing with select (Zidx x₁) x
  ...| nothing = ⊥-elim (Maybe-⊥ (sym hip))
  ...| just h with <M>-elim hip
  ...| r , s , t with res-symmetric h q r t
  ...| f , res rewrite res | s
    = (λ { (D-μ-A x p) → D-μ-A x (f p) ; x → f x }) , refl
  res-symmetric (D-μ-dwn p x) (D-μ-rmv x₁ q) pq hip
     | just (mu x') | just r with select (Zidx x₁) x
  ...| nothing = ⊥-elim (Maybe-⊥ (sym hip))
  ...| just h with res-symmetric h q pq hip
  ...| f , res rewrite res
    = (D-μ-rmv x₁) ∘ f , refl
 
  
  res-symmetric (D-μ-rmv x p) (D-μ-dwn q x₁) pq hip
    with D-dst (D-μ-dwn q x₁)
  ...| nothing = ⊥-elim (Maybe-⊥ (sym hip))
  ...| just (mu x')
    with match x x'
  res-symmetric (D-μ-rmv x p) (D-μ-dwn q x₁) pq hip
     | just (mu x') | nothing with select (Zidx x) x₁
  ...| nothing = ⊥-elim (Maybe-⊥ (sym hip))
  ...| just h with <M>-elim hip
  ...| r , s , t with res-symmetric p h r t
  ...| f , res rewrite res | s
     = (λ { (D-μ-A x p) → D-μ-A x (f p) ; x → f x })
     , refl
  res-symmetric (D-μ-rmv x p) (D-μ-dwn q x₁) pq hip
     | just (mu x') | just r with select (Zidx x) x₁
  ...| nothing = ⊥-elim (Maybe-⊥ (sym hip))
  ...| just h with <M>-elim hip
  ...| m , n , o with res-symmetric p h m o
  res-symmetric (D-μ-rmv x p) (D-μ-dwn q x₁) .(D-μ-rmv x m) hip
     | just (mu x') | just r | just h
     | m , refl , o | f , res rewrite res
     = (λ { (D-μ-rmv x k) → f k ; x → f x }) , refl
  
  res-symmetric (D-μ-rmv x p) (D-μ-rmv x₁ q) pq hip
    with x ≟-Ctx x₁ | x₁ ≟-Ctx x
  ...| no  a | yes b = ⊥-elim (a (sym b))
  ...| yes a | no  b = ⊥-elim (b (sym a))
  res-symmetric (D-μ-rmv x p) (D-μ-rmv x₁ q) pq hip
     | no  a | no  b with <M>-elim hip
  ...| m , n , o with res-symmetric p q m o
  ...| f , res rewrite res | n
     = (λ { (D-μ-A x p) → D-μ-A x (f p); x → f x}) , refl
  res-symmetric (D-μ-rmv x p) (D-μ-rmv x₁ q) pq hip
     | yes a | yes b with res-symmetric p q pq hip
  ...| f , res rewrite res
     = f , refl
\end{code}
