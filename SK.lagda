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
    ind$ : ∀{A B}{u : I.Tm (A I.⇒ B)}{v : I.Tm A} →
           ind {B} {indT B} (u I.$ v) ≡ _$•_ {A} {B} {indT A} {indT B} (ind u) (ind v)
    indK : ∀{A B} →
           ind (I.K {A} {B}) ≡ K• {A} {B} {indT A} {indT B}
    indS : ∀{A B C} →
           ind (I.S {A} {B} {C}) ≡ S• {A} {B} {C} {indT A} {indT B} {indT C}
    {-# REWRITE ind$ indK indS #-}

-- Then we have to describe the normal forms (model without equations)
-- Basically we can see them as all terms of SK where applications are all partials:

module _ where
  open I
  
  data NF : I.Ty → Set where
    K₀ : ∀{A B} → NF (A ⇒ B ⇒ A)
    K₁ : ∀{A B} → NF A → NF (B ⇒ A)
    S₀ : ∀{A B C} → NF ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    S₁ : ∀{A B C} → NF (A ⇒ B ⇒ C) → NF ((A ⇒ B) ⇒ A ⇒ C)
    S₂ : ∀{A B C} → NF (A ⇒ B ⇒ C) → NF (A ⇒ B) → NF (A ⇒ C)

  -- Then we can give the translations from a form to another :

  -- Inclusion

  ⌜_⌝ : ∀{A} → NF A → Tm A
  ⌜ K₀ ⌝ = K
  ⌜ K₁ u ⌝ = K $ ⌜ u ⌝
  ⌜ S₀ ⌝ = S
  ⌜ S₁ u ⌝ = S $ ⌜ u ⌝
  ⌜ S₂ u v ⌝ = S $ ⌜ u ⌝ $ ⌜ v ⌝

-- Normalisation

NormProof : DepModel
NormProof = record
  { Ty•  = λ A → Σ (I.Tm A → Set) (λ RED → (u : I.Tm A) → RED u → NF A)
  ; ι•   = (λ _ → Lift ⊥), λ _ p → ⊥-elim (unfold p) -- there is no term of type ι
  ; _⇒•_ = λ {A}{B} (REDA , _) (REDB , _) →
             (λ u → ((v : I.Tm A) → REDA v → REDB (u I.$ v)) × NF (A I.⇒ B)) ,
             (λ u u• → pr₂ u•)
  ; Tm•  = pr₁
  ; _$•_ = λ {_}{_}{_}{_}{_}{v} u• v• →
           (pr₁ u• v v•)
  ; K•   = λ {_}{_}{A•} →
           (λ u u• → (λ v v• → transp⟨ pr₁ A• ⟩ (symetry I.Kβ) u•) ,
                     (K₁ (pr₂ A• u u•))) ,
           K₀
  ; S•   = λ {A}{B}{C}{A•}{B•}{C•} →
           (λ f f• → (λ g g• → (λ x x• → transp⟨ pr₁ C• ⟩ (symetry I.Sβ) (pr₁ (pr₁ f• x x•) (g I.$ x) (pr₁ g• x x• ))) ,
                               (S₂ (pr₂ f•) (pr₂ g•))) ,
                     (S₁ (pr₂ f•))) ,
           S₀
  ; Kβ•  = λ {_}{_}{A•} → transptransp (pr₁ A•) (symetry I.Kβ)
  ; Sβ•  = λ {_}{_}{_}{_}{_}{C•} → transptransp (pr₁ C•) (symetry I.Sβ){I.Sβ}
  }
module NormProof = DepModel NormProof

norm : ∀{A} → I.Tm A → NF A
norm {A} u = pr₂ (NormProof.indT A) u (NormProof.ind {A}{NormProof.indT A} u)

-- Homomorphism

-- refl should work because of rewriting rules but I have to specify a ton of implicit parameters

normK₀Morph : ∀{A}{B} → norm (I.K {A}{B}) ≡ (K₀ {A}{B})
normK₀Morph = refl

test : ∀{A}{B} → NormProof.K• {A}{B}{NormProof.indT A}{NormProof.indT B} ≡
                 NormProof.ind {A I.⇒ B I.⇒ A}{NormProof.indT (A I.⇒ B I.⇒ A)} (I.K {A}{B})
test = refl
  
normK₁Morph : ∀{A}{B}{u : I.Tm A} → norm (I.K I.$ u) ≡ (K₁ {A}{B} (norm u))
normK₁Morph {A}{B}{u} =
   let A• = NormProof.indT A in
   let B• = NormProof.indT B in
   pr₂ (NormProof.ind {B I.⇒ A}{B• NormProof.⇒• A•} (I.K I.$ u)) ≡⟨ cong⟨ pr₂ ⟩ (NormProof.ind$ {A}{B I.⇒ A}{I.K}{u}) ⟩
   refl

normSMorph : ∀{A}{B}{C} → norm (I.S {A}{B}{C}) ≡ (S₀ {A}{B}{C})
normSMorph = refl

normS₁Morph : ∀{A}{B}{C}{f : I.Tm (A I.⇒ B I.⇒ C)} → norm (I.S I.$ f) ≡ S₁ (norm f)
normS₁Morph {A}{B}{C}{f} =
  let A• = NormProof.indT A in
  let B• = NormProof.indT B in
  let C• = NormProof.indT C in
  pr₂ (NormProof.ind {(A I.⇒ B) I.⇒ A I.⇒ C}{(A• NormProof.⇒• B•) NormProof.⇒• A• NormProof.⇒• C•} (I.S I.$ f))
    ≡⟨ cong⟨ pr₂ ⟩ (NormProof.ind$ {A I.⇒ B I.⇒ C}{(A I.⇒ B) I.⇒ A I.⇒ C}{I.S}{f}) ⟩
  refl

normS₂Morph : ∀{A}{B}{C}{f : I.Tm (A I.⇒ B I.⇒ C)}{g : I.Tm (A I.⇒ B)} → norm (I.S I.$ f I.$ g) ≡ S₂ (norm f) (norm g)
normS₂Morph {A}{B}{C}{f}{g} =
  let A• = NormProof.indT A in
  let B• = NormProof.indT B in
  let C• = NormProof.indT C in
  pr₂ (NormProof.ind {A I.⇒ C}{A• NormProof.⇒• C•} (I.S I.$ f I.$ g))
    ≡⟨ cong⟨ pr₂ ⟩ (NormProof.ind$ {A I.⇒ B}{A I.⇒ C}{I.S I.$ f}{g}) ⟩
  pr₂ (pr₁ (NormProof.ind {(A I.⇒ B) I.⇒ A I.⇒ C}{(A• NormProof.⇒• B•) NormProof.⇒• A• NormProof.⇒• C•}(I.S I.$ f)) g (NormProof.ind {A I.⇒ B}{A• NormProof.⇒• B•} g))
    ≡⟨ cong⟨ (λ x → pr₂ (pr₁ x g (NormProof.ind {A I.⇒ B}{A• NormProof.⇒• B•} g))) ⟩ (NormProof.ind$ {A I.⇒ B I.⇒ C}{(A I.⇒ B) I.⇒ A I.⇒ C}{I.S}{f}) ⟩
  refl

-- Stability

normStability : ∀{A} → (nf : NF A) → norm ⌜ nf ⌝ ≡ nf
normStability K₀       = refl
normStability (K₁ u)   = norm ⌜ K₁ u ⌝     ≡⟨ normK₁Morph ⟩
                         K₁ (norm ⌜ u ⌝)   ≡⟨ cong⟨ K₁ ⟩ (normStability u) ⟩
                         refl
normStability S₀       = refl
normStability (S₁ f)   = norm ⌜ S₁ f ⌝     ≡⟨ normS₁Morph ⟩
                         S₁ (norm ⌜ f ⌝)   ≡⟨ cong⟨ S₁ ⟩ (normStability f) ⟩
                         refl
normStability (S₂ f g) = norm ⌜ S₂ f g ⌝               ≡⟨ normS₂Morph ⟩
                         S₂ (norm ⌜ f ⌝) (norm ⌜ g ⌝)  ≡⟨ cong⟨ (λ x → S₂ x (norm ⌜ g ⌝)) ⟩ (normStability f) ⟩
                         S₂ f (norm ⌜ g ⌝)             ≡⟨ cong⟨ (S₂ f) ⟩ (normStability g) ⟩
                         refl

\end{code}
