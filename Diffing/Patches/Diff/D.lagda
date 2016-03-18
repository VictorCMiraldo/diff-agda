\begin{code}
open import Prelude
open import Diffing.Universe

module Diffing.Patches.Diff.D where
\end{code}

%<*ValU>
\begin{code}
  ValU : {n : ℕ} → U (suc n) → T n → Set
  ValU ty t = ElU ty (u1 ∷ t)
\end{code}
%</ValU>

\begin{code}
  mutual
\end{code}

%<*D-type>
\begin{code}
    data D {a}(A : {n : ℕ} → T n → U n → Set a) 
      : {n : ℕ} → T n → U n → Set a where
\end{code}
%</D-type>

%<*D-A-def>
\begin{code}
      D-A    : {n : ℕ}{t : T n}{ty : U n} → A t ty → D A t ty
\end{code}
%</D-A-def>

%<*D-void-def>
\begin{code}
      D-unit : {n : ℕ}{t : T n} → D A t u1
\end{code}
%</D-void-def>

%<*D-sum-def>
\begin{code}
      D-inl  : {n : ℕ}{t : T n}{a b : U n} 
             → D A t a → D A t (a ⊕ b)
      D-inr  : {n : ℕ}{t : T n}{a b : U n} 
             → D A t b → D A t (a ⊕ b)
      D-setl  : {n : ℕ}{t : T n}{a b : U n} 
              → ElU a t → ElU b t → D A t (a ⊕ b)
      D-setr  : {n : ℕ}{t : T n}{a b : U n} 
              → ElU b t → ElU a t → D A t (a ⊕ b)
\end{code}
%</D-sum-def>

%<*D-pair-def>
\begin{code}
      D-pair : {n : ℕ}{t : T n}{a b : U n} 
             → D A t a → D A t b → D A t (a ⊗ b)
\end{code}
%</D-pair-def>

%<*D-mu-def>
\begin{code}
      D-mu : {n : ℕ}{t : T n}{a : U (suc n)}
           → Dμ A t a 1 1 → D A t (μ a)
\end{code}
%</D-mu-def>

%<*D-rest-def>
\begin{code}
      D-def : {n : ℕ}{t : T n}{F : U (suc n)}{x : U n} 
            → D A (x ∷ t) F → D A t (def F x)
      D-top : {n : ℕ}{t : T n}{a : U n}
            → D A t a → D A (a ∷ t) var
      D-pop : {n : ℕ}{t : T n}{a b : U n}
            → D A t b → D A (a ∷ t) (wk b)
\end{code}
%</D-rest-def>


%<*Dmu-type>
\begin{code}
    data Dμ {a}(A : {n : ℕ} → T n → U n → Set a)
            {n : ℕ}(t : T n)(ty : U (suc n)) : ℕ → ℕ → Set a 
         where
\end{code}
%</Dmu-type>

%<*Dmu-A-def>
\begin{code}
      Dμ-A   : {i j : ℕ}
             → A t (μ ty) → Dμ A t ty i j → Dμ A t ty i j
\end{code}
%</Dmu-A-def>

%<*Dmu-def>
\begin{code}
      Dμ-del : {i j : ℕ}(a : ValU ty t) 
             → Dμ A t ty (ar 0 a + i) j → Dμ A t ty (suc i) j
      Dμ-ins : {i j : ℕ}(a : ValU ty t) 
             → Dμ A t ty i (ar 0 a + j) → Dμ A t ty i (suc j)
      Dμ-dwn : {i j : ℕ}(d : D A (u1 ∷ t) ty)
             → Dμ A t ty (#i 0 d + i) (#o 0 d + j)
             → Dμ A t ty (suc i) (suc j)
      Dμ-end : Dμ A t ty 0 0
\end{code}
%</Dmu-def>

  A diff has two arities. The input arity
  corresponds to the arity of the domain element,
  whereas the output arity corresponds to the arity of
  the target element.

%<*dmu-arity-type>
\begin{code}
    #i* #o* : ∀{a}{n i j : ℕ}{t : T n}{ty : U (suc n)}
              {A : {n : ℕ} → T n → U n → Set a}
            → ℕ → Dμ A t ty i j → ℕ
\end{code}
%</dmu-arity-type>
%<*d-arity-type>
\begin{code}
    #i #o : ∀{a}{n : ℕ}{t : T n}{ty : U n}{A : {n : ℕ} → T n → U n → Set a}
          → ℕ → D A t ty → ℕ
\end{code}
%</d-arity-type>
\begin{code}
    #i i (D-A x) = 0
    #i i D-unit = 0
    #i i (D-inl d) = #i i d
    #i i (D-inr d) = #i i d
    #i i (D-setl x _) = ar i x
    #i i (D-setr x _) = ar i x
    #i i (D-pair da db) = #i i da + #i i db
    #i i (D-mu x) = #i* i x
    #i i (D-def d) = #i (suc i) d
    #i zero (D-top d) = 1
    #i (suc i) (D-top d) = #i i d
    #i zero (D-pop d) = 0
    #i (suc i) (D-pop d) = #i i d

    #o i (D-A x) = 0
    #o i D-unit = 0
    #o i (D-inl d) = #o i d
    #o i (D-inr d) = #o i d
    #o i (D-setl _ x) = ar i x
    #o i (D-setr _ x) = ar i x
    #o i (D-pair da db) = #o i da + #o i db
    #o i (D-mu x) = #o* i x
    #o i (D-def d) = #o (suc i) d
    #o zero (D-top d) = 1
    #o (suc i) (D-top d) = #o i d
    #o zero (D-pop d) = 0
    #o (suc i) (D-pop d) = #o i d

    #i* i (Dμ-A x d) = #i* i d
    #i* i (Dμ-del x d) = ar (suc i) x + #i* i d
    #i* i (Dμ-ins x d) = #i* i d
    #i* i (Dμ-dwn dx d) = #i (suc i) dx + #i* i d
    #i* i Dμ-end = 0

    #o* i (Dμ-A x d) = 0
    #o* i (Dμ-del x d) = #o* i d
    #o* i (Dμ-ins x d) = ar (suc i) x + #o* i d
    #o* i (Dμ-dwn dx d) = #o (suc i) dx + #o* i d
    #o* i Dμ-end = 0
\end{code}

  Some synonyms for patches.

%<*Patch-def>
\begin{code}
  ⊥ₚ : {n : ℕ} → T n → U n → Set
  ⊥ₚ {_} _ _ = ⊥

  Patch : {n : ℕ} → T n → U n → Set
  Patch t ty = D ⊥ₚ t ty
       
  Patchμ : {n : ℕ} → T n → U (suc n) → Set
  Patchμ t ty = Dμ ⊥ₚ t ty 1 1
\end{code}
%</Patch-def>

  Finally, a bunch of usefull lemmas to manipulate indices
  and call some well-known facts (meaning that we proved their
  general version on Diffing.Universe.Operations.Properties)

\begin{code}
  module Substs where
    open import Data.List.Properties using (length-++)
  
    μ-length-arity-lemma
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (y : ElU (μ ty) t)(ys : List (ElU (μ ty) t))
      → length (μ-ch y ++ ys) ≡ μ-ar y + length ys
    μ-length-arity-lemma y ys 
      = trans (length-++ (μ-ch y)) (cong₂ _+_ (μ-open-ar-lemma y) refl)

    μ-lal
      : {n : ℕ}{t : T n}{ty : U (suc n)}
      → (y : ElU (μ ty) t){ys : List (ElU (μ ty) t)}
      → length (μ-ch y ++ ys) ≡ μ-ar y + length ys
    μ-lal y {ys} = μ-length-arity-lemma y ys

    μ-subst-i : {n i j k : ℕ}{t : T n}{ty : U (suc n)}
            → k ≡ i
            → Dμ ⊥ₚ t ty k j
            → Dμ ⊥ₚ t ty i j
    μ-subst-i prf = subst (λ P → Dμ _ _ _ P _) prf

    μ-subst-o : {n i j k : ℕ}{t : T n}{ty : U (suc n)}
            → k ≡ i
            → Dμ ⊥ₚ t ty j k 
            → Dμ ⊥ₚ t ty j i
    μ-subst-o prf = subst (λ P → Dμ _ _ _ _ P) prf

    μ-subst-io : {n i j k l : ℕ}{t : T n}{ty : U (suc n)}
               → l ≡ j
               → k ≡ i
               → Dμ ⊥ₚ t ty l k 
               → Dμ ⊥ₚ t ty j i
    μ-subst-io pi po = μ-subst-i pi ∘ μ-subst-o po

    #i*-substo-lemma 
      : {n i j k : ℕ}{t : T n}{ty : U (suc n)}
      → (p : k ≡ i)(d : Dμ ⊥ₚ t ty j k)(v : ℕ)
      → #i* v (μ-subst-o p d) ≡ #i* v d
    #i*-substo-lemma refl d v = refl

    #i*-substi-lemma
      : {n i j k : ℕ}{t : T n}{ty : U (suc n)}
      → (p : k ≡ i)(d : Dμ ⊥ₚ t ty k j)(v : ℕ)
      → #i* v (μ-subst-i p d) ≡ #i* v d
    #i*-substi-lemma refl d v = refl
  
    #i*-substio-lemma 
      : {n i j k l : ℕ}{t : T n}{ty : U (suc n)}
      → (p : k ≡ i)(q : j ≡ l)(d : Dμ ⊥ₚ t ty k j)(v : ℕ)
      → #i* v (μ-subst-io p q d) ≡ #i* v d
    #i*-substio-lemma refl refl d v = refl

    #o*-substo-lemma 
      : {n i j k : ℕ}{t : T n}{ty : U (suc n)}
      → (p : k ≡ i)(d : Dμ ⊥ₚ t ty j k)(v : ℕ)
      → #o* v (μ-subst-o p d) ≡ #o* v d
    #o*-substo-lemma refl d v = refl

    #o*-substi-lemma
      : {n i j k : ℕ}{t : T n}{ty : U (suc n)}
      → (p : k ≡ i)(d : Dμ ⊥ₚ t ty k j)(v : ℕ)
      → #o* v (μ-subst-i p d) ≡ #o* v d
    #o*-substi-lemma refl d v = refl
  
    #o*-substio-lemma 
      : {n i j k l : ℕ}{t : T n}{ty : U (suc n)}
      → (p : k ≡ i)(q : j ≡ l)(d : Dμ ⊥ₚ t ty k j)(v : ℕ)
      → #o* v (μ-subst-io p q d) ≡ #o* v d
    #o*-substio-lemma refl refl d v = refl
\end{code}
