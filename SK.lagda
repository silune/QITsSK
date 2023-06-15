\begin{code}

{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import Equality
open import Logic

module SK where

-- First the initial model consists of
  -- Types
  -- Terms
  -- Reduction Rules

module I where
  infixr 5 _⇒_
  infixl 5 _$_

  data Ty : Set where
    ι   : Ty
    _⇒_ : Ty → Ty → Ty

  postulate
    Tm  : Ty → Set
    _$_ : {A B : Ty} → Tm (A ⇒ B) → Tm A → Tm B
    K   : {A B : Ty} → Tm (A ⇒ B ⇒ A)
    S   : {A B C : Ty} → Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    Kβ  : {A B : Ty}{x : Tm A}{y : Tm B} → K $ x $ y ≡ x
    Sβ  : {A B C : Ty}{f : Tm (A ⇒ B ⇒ C)}{g : Tm (A ⇒ B)}{x : Tm A} → S $ f $ g $ x ≡ f $ x $ (g $ x)

-- Then we can define the general form of a Model and a Dependent Model
-- (Maybe it could be interesting to define Models without postulate using Dependent Models ?)

record Model {l l'} : Set (lsuc (l ⊔ l')) where
  infixr 5 _⇒_
  infixl 5 _$_

  field
    Ty  : Set l
    ι   : Ty
    _⇒_ : Ty → Ty → Ty
    Tm  : Ty → Set l'
    _$_ : ∀{A B}  → Tm (A ⇒ B) → Tm A → Tm B
    K   : ∀{A B}   → Tm (A ⇒ B ⇒ A)
    S   : ∀{A B C} → Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    Kβ  : ∀{A B}{u : Tm A}{v : Tm B} →
          K $ u $ v ≡ u
    Sβ  : ∀{A B C}{f : Tm (A ⇒ B ⇒ C)}{g : Tm (A ⇒ B)}{u : Tm A} →
          S $ f $ g $ u ≡ f $ u $ (g $ u)
  
  ⟦_⟧T : I.Ty → Ty
  ⟦ I.ι ⟧T = ι
  ⟦ A I.⇒ B ⟧T = ⟦ A ⟧T ⇒ ⟦ B ⟧T

  postulate
    ⟦_⟧ : ∀{A} → I.Tm A → Tm ⟦ A ⟧T
    ⟦$⟧ : ∀{A B} → {f : I.Tm (A I.⇒ B)} → {x : I.Tm A} → ⟦ f I.$ x ⟧ ≡ ⟦ f ⟧ $ ⟦ x ⟧
    ⟦K⟧ : ∀{A B} → ⟦ I.K {A} {B} ⟧ ≡ K {⟦ A ⟧T} {⟦ B ⟧T}
    ⟦S⟧ : ∀{A B C} → ⟦ I.S {A} {B} {C} ⟧ ≡ S {⟦ A ⟧T} {⟦ B ⟧T} {⟦ C ⟧T}
  {-# REWRITE ⟦$⟧ ⟦K⟧ ⟦S⟧ #-}

record DepModel {l} {l'} : Set (lsuc (l ⊔ l')) where
  infixr 5 _⇒•_
  infixl 5 _$•_

  field
    Ty•  : I.Ty → Set l
    ι•   : Ty• I.ι
    _⇒•_ : ∀{A B} → Ty• A → Ty• B → Ty• (A I.⇒ B)
    Tm•  : ∀{A} → Ty• A → I.Tm A → Set l'
    _$•_ : ∀{A B}{A• : Ty• A}{B• : Ty• B}{u : I.Tm (A I.⇒ B)}{v : I.Tm A} →
           Tm• (A• ⇒• B•) u → Tm• A• v  → Tm• B• (u I.$ v)
    K•   : ∀{A B}{A• : Ty• A}{B• : Ty• B} →
           Tm• (A• ⇒• B• ⇒• A•) I.K
    S•   : ∀{A B C}{A• : Ty• A}{B• : Ty• B}{C• : Ty• C} →
           Tm• ((A• ⇒• B• ⇒• C•) ⇒• (A• ⇒• B•) ⇒• A• ⇒• C•) I.S
    Kβ•  : ∀{A B}{A• : Ty• A}{B• : Ty• B}{u : I.Tm A}{u• : Tm• A• u}{v : I.Tm B}{v• : Tm• B• v} →
           transp⟨ Tm• A• ⟩ I.Kβ (K• $• u• $• v•) ≡ u•
    Sβ•  : ∀{A B C}{A• : Ty• A}{B• : Ty• B}{C• : Ty• C}
            {f : I.Tm (A I.⇒ B I.⇒ C)}{f• : Tm• (A• ⇒• B• ⇒• C•) f}
            {g : I.Tm (A I.⇒ B)}{g• : Tm• (A• ⇒• B•) g}
            {u : I.Tm A}{u• : Tm• A• u} →
            transp⟨ Tm• C• ⟩ I.Sβ (S• $• f• $• g• $• u•) ≡ f• $• u• $• (g• $• u•)

  indT : (A : I.Ty) → Ty• A
  indT I.ι       = ι•
  indT (A I.⇒ B) = (indT A) ⇒• (indT B)
    
  postulate
    ind  : ∀{A}{A• : Ty• A} → (u : I.Tm A) → Tm• A• u
    ind$ : ∀{A B}{u : I.Tm (A I.⇒ B)}{v : I.Tm A} → ind {B} {indT B} (u I.$ v) ≡ _$•_ {A} {B} {indT A} {indT B} (ind u) (ind v)
    indK : ∀{A B} → ind (I.K {A} {B}) ≡ K• {A} {B} {indT A} {indT B}
    indS : ∀{A B C} → ind (I.S {A} {B} {C}) ≡ S• {A} {B} {C} {indT A} {indT B} {indT C}
  {-# REWRITE ind$ indK indS #-}

\end{code}
