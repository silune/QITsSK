\begin{code}

-- Definition for propositional equality with some properties

{-# OPTIONS --prop --rewriting #-}

open import Logic

module Equality where

  infix 4 _≡_
  infixr 2 _≡⟨_⟩_

  id : ∀{l}{A : Set l} → A → A
  id = λ x → x

  -- Equality

  data _≡_ {l}{A : Set l}(x : A) : A → Prop l where
    refl : x ≡ x

  {-# BUILTIN REWRITE _≡_ #-}

  record Lift {l}(A : Prop l) : Set l where
    constructor ⟪_⟫
    field unfold : A
  open Lift public
    
  -- Properities

  symetry : ∀{l}{A : Set l}{x y : A} → x ≡ y → y ≡ x
  symetry refl = refl

  transitivity : ∀{l}{A : Set l}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  transitivity refl refl = refl

  _≡⟨_⟩_ : ∀{l}{A : Set l}{y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ eqy ⟩ eqz = transitivity eqy eqz

  -- (lemma 2.2.1 HoTT)
  cong⟨_⟩ : ∀{l}{A : Set l}{l'}{B : Set l'}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
  cong⟨ f ⟩ refl = refl
  
  -- (lemma 2.3.2 HoTT) (need to be postulate when working with Prop instead of Set ?)
  postulate transp⟨_⟩ : ∀{l}{A : Set l}{l'}(P : A → Set l'){x y : A} → x ≡ y → P x → P y
  -- transp⟨ P ⟩ refl px = px

  -- (why ?)
  postulate transprefl : ∀{l}{A : Set l}{l'}{P : A → Set l'}{a : A}{e : a ≡ a}{p : P a} → transp⟨ P ⟩ e p ≡ p
  {-# REWRITE transprefl #-}

  -- (lemma 2.3.5 HoTT)
  transpconst⟨_⟩ : ∀{l}{A : Set l}{l'}{P : Set l'}{x y : A}{eq : x ≡ y} → (p : P) → transp⟨ (λ _ → P) ⟩ eq p ≡ p
  transpconst⟨_⟩ {eq = refl} p = refl

  -- How to do this ??
  postulate transpEq : ∀{l}{A : Set l}{l'}{P : Set l'}{x y : A}{eq : x ≡ y}{p p' : P} -> p ≡ p' → transp⟨ (λ _ → P) ⟩ eq p ≡ p'

  -- Functional extensionality (Axiom 2.9.3 HoTT)

  postulate funext  : ∀{l}{A : Set l}{l'}{B : Set l'}{f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
  funexti : ∀{l}{A : Set l}{l'}{B : Set l'}{f g : A → B} → ({x : A} → f x ≡ g x) → f ≡ g
  funexti p = funext (λ a → p {x = a})


\end{code}
