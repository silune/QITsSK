\begin{code}

{-# OPTIONS --prop --rewriting #-}

open import Logic
open import Equality

module Nat where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

NatDecEq : (n n' : ℕ) → (n ≡ n') ∨ ¬ (n ≡ n')
NatDecEq (zero  ) (zero  ) = left refl
NatDecEq (succ a) (zero  ) = right (λ ())
NatDecEq (zero  ) (succ b) = right (λ ())
NatDecEq (succ a) (succ b) with NatDecEq a b
...            | left refl = left refl
...            | right a≠b = right (λ {refl → a≠b refl})

𝟘 : ℕ
𝟘 = zero
𝟙 : ℕ
𝟙 = succ zero
𝟚 : ℕ
𝟚 = succ 𝟙
𝟛 : ℕ
𝟛 = succ 𝟚
𝟜 : ℕ
𝟜 = succ 𝟛
𝟝 : ℕ
𝟝 = succ 𝟜

-- We can define Labeled (on ℕ) Binary Trees, and decidable equality on them :

data LBT : Set where
  Leaf : ℕ → LBT
  Node : LBT → LBT → LBT

LBTDecEq : (t t' : LBT) → (t ≡ t') ∨ ¬ (t ≡ t')
LBTDecEq (Leaf a) (Leaf b) with NatDecEq a b
... | left refl = left refl
... | right a≠b = right (λ {refl → a≠b refl})
LBTDecEq (Leaf _) (Node _ _) = right (λ ())
LBTDecEq (Node _ _) (Leaf _) = right (λ ())
LBTDecEq (Node t₁ t₂) (Node t₁' t₂') with LBTDecEq t₁ t₁' | LBTDecEq t₂ t₂'
... | left refl    | left refl   = left refl
... | right t₁≠t₁' | _            = right (λ {refl → t₁≠t₁' refl})
... | _            | right t₂≠t₂' = right (λ {refl → t₂≠t₂' refl})

\end{code}
