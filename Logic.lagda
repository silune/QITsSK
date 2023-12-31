\begin{code}

{-# OPTIONS --prop #-}

open import Agda.Primitive

module Logic where

  infixr 4 _,_
  infixr 5 _∨_
  infixr 6 _∧_

  -- Unit type
  data ⊤ : Prop where
    triv : ⊤

  -- Empty type Prop
  data ⊥ : Prop where

  ⊥-elim : ∀{l}{A : Set l} → ⊥ → A
  ⊥-elim ()

  -- Empty type Set
  data ∅ {l} : Set l where

  ∅-elim : ∀{l}{l'}{A : Set l} → ∅ {l'} → A
  ∅-elim ()

  ∅-elim-prop : ∀{l}{l'}{A : Prop l} → ∅ {l'} → A
  ∅-elim-prop ()
  
  -- Negation
  ¬ : Prop → Prop
  ¬ A = A → ⊥

  -- Conjunction
  data _∧_ (A B : Prop) : Prop where
    _∧,_ : A → B → A ∧ B

  -- Disjunction
  data _∨_ (A B : Prop) : Prop where
    left  : A → A ∨ B
    right : B → A ∨ B

  -- Existential Quantifier

  record Σ {l}{l'} (A : Set l) (B : A → Set l') : Set (l ⊔ l') where
    constructor _,_
    field
      pr₁ : A
      pr₂ : B pr₁
  open Σ public

  _×_ : ∀{l}{l'} (A : Set l) (B : Set l') → Set (l ⊔ l')
  A × B = Σ A (λ _ → B)

  data _⨄_ {l}{l'} (A : Set l) (B : Set l') : Set (l ⊔ l') where
    ι₁ : A → A ⨄ B
    ι₂ : B → A ⨄ B
       

\end{code}
