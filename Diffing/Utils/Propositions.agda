open import Prelude
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties.Simple using (+-comm)
open import Data.List using (drop)

module Diffing.Utils.Propositions where

  suc-inj : ∀{m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  -- We can always express a list which has
  -- at least n elements as a concatenation.
  list-split-lemma 
    : {A : Set}{n : ℕ}{l : List A}
    → n ≤ length l
    → Σ (List A × List A)
        (λ ls → length (p1 ls) ≡ n × l ≡ (p1 ls) ++ (p2 ls))
  list-split-lemma {n = zero} {l = l} n≤l 
    = ([] , l) , refl , refl
  list-split-lemma {n = suc n} {[]} ()
  list-split-lemma {n = suc n} {x ∷ l} (s≤s n≤l)
    with list-split-lemma {n = n} {l = l} n≤l
  ...| (la , lb) , pla , plb 
     = ((x ∷ la) , lb) , ((cong suc pla) , (cong (_∷_ x) plb))

  length-++-stable : {A : Set}{l j : List A}{n : ℕ}
                   → length (l ++ j) ≡ length l + n
                   → length j ≡ n
  length-++-stable {l = []} prf = prf
  length-++-stable {l = x ∷ l} {j} prf  
    = length-++-stable {l = l} {j} (suc-inj prf)

  drop[]≡[] : {A : Set}{n : ℕ} → drop {A = A} n [] ≡ []
  drop[]≡[] {n = zero} = refl
  drop[]≡[] {n = suc n} = refl
  
  drop-+-comm
    : {A : Set}{l : List A}(n m : ℕ) → drop (n + m) l ≡ drop n (drop m l)
  drop-+-comm zero m = refl
  drop-+-comm {A} {l = []} (suc n) m with drop[]≡[] {A} {m}
  ...| r rewrite r = refl
  drop-+-comm {l = x ∷ l} (suc n) zero 
    rewrite (+-comm n zero) = refl
  drop-+-comm {l = x ∷ l} (suc n) (suc m) with drop-+-comm {l = l} (suc n) m 
  ...| r rewrite sym r | +-comm n (suc m) | +-comm n m = refl

  drop-++-id : {A : Set}{l j : List A}
             → drop (length l) (l ++ j) ≡ j
  drop-++-id {l = []} = refl
  drop-++-id {l = x ∷ l} {j} = drop-++-id {l = l} {j = j}

  nat-split-lemma 
    : {m n o : ℕ} → m + n ≤ o → m ≤ o × n ≤ o
  nat-split-lemma {zero} prf = z≤n , prf
  nat-split-lemma {suc m} {o = zero} ()
  nat-split-lemma {suc m} {o = suc o} (s≤s prf)
    with nat-split-lemma {m} {o = o} prf
  ...| p1 , p2 = s≤s p1 , s≤ p2
    where
      s≤ : {n m : ℕ} → n ≤ m → n ≤ suc m
      s≤ z≤n     = z≤n
      s≤ (s≤s p) = s≤s (s≤ p)

  nat-factor-lemma : {m n o : ℕ} → m + n ≡ o → m ≤ o 
  nat-factor-lemma {zero} prf = z≤n
  nat-factor-lemma {suc m} refl = s≤s (nat-factor-lemma refl)

  nat≡≤ : {m n : ℕ} → m ≡ n → m ≤ n
  nat≡≤ {zero} refl = z≤n
  nat≡≤ {suc m} refl = s≤s (nat≡≤ refl)

  nat-≤-elim : {n m : ℕ} → m ≤ suc n → (m ≡ suc n → ⊥) → m ≤ n
  nat-≤-elim {_} {zero} prf n≢m         = z≤n
  nat-≤-elim {zero} {suc .0} (s≤s z≤n) n≢m = ⊥-elim (n≢m refl)
  nat-≤-elim {suc n} {suc m} (s≤s prf) n≢m 
    = s≤s (nat-≤-elim prf (n≢m ∘ cong suc))

  nat-≤-step : {n m : ℕ} → n ≤ m → n ≤ suc m
  nat-≤-step z≤n       = z≤n
  nat-≤-step (s≤s prf) = s≤s (nat-≤-step prf)

  data LEQ : ℕ → ℕ → Set where
    LEQ-refl : {n : ℕ} → LEQ n n
    LEQ-step : {n m : ℕ} → LEQ n m → LEQ n (suc m)

  ≤-LEQ : {n m : ℕ} → n ≤ m → LEQ n m
  ≤-LEQ {n} {m} prf with n ≟-ℕ m
  ...| yes n≡m rewrite n≡m = LEQ-refl
  ≤-LEQ {.0} {zero} z≤n | no n≢m = ⊥-elim (n≢m refl)
  ≤-LEQ {n} {suc m} prf | no n≢m = LEQ-step (≤-LEQ (nat-≤-elim prf n≢m))

  LEQ-≤ : {n m : ℕ} → LEQ n m → n ≤ m
  LEQ-≤ {zero} LEQ-refl = z≤n
  LEQ-≤ {suc n} LEQ-refl = s≤s (LEQ-≤ {n} LEQ-refl)
  LEQ-≤ (LEQ-step leq) = nat-≤-step (LEQ-≤ leq)

  Δ : {m n : ℕ} → LEQ m n → ℕ 
  Δ LEQ-refl     = 0
  Δ (LEQ-step p) = suc (Δ p)

  Δ-correct : {m n : ℕ} → (p : LEQ m n) → n ≡ Δ p + m
  Δ-correct LEQ-refl     = refl
  Δ-correct (LEQ-step p) = cong suc (Δ-correct p)

  Δ-Fin : {m n : ℕ} → (p : LEQ m n) → Fin (suc (Δ p))
  Δ-Fin LEQ-refl = fz
  Δ-Fin (LEQ-step p) = fs (Δ-Fin p)

  ++-assoc : {A : Set}{x y z : List A}
           → (x ++ y) ++ z ≡ x ++ (y ++ z)
  ++-assoc {x = []} = refl
  ++-assoc {x = x ∷ xs} = cong (_∷_ x) (++-assoc {x = xs})
