\begin{code}

{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import Equality
open import Logic

module SK_bool where

--------------------------------------------------

-- First the initial model consists of
  -- Types
  -- Terms
  -- Reduction Rules

module I where
  infixr 5 _⇒_
  infixl 5 _$_

  data Ty : Set where
    ι    : Ty
    Bool : Ty
    _⇒_  : Ty → Ty → Ty

  postulate
    Tm  : Ty → Set
    _$_ : {A B : Ty} → Tm (A ⇒ B) → Tm A → Tm B
    K   : {A B : Ty} → Tm (A ⇒ B ⇒ A)
    S   : {A B C : Ty} → Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    tt  : Tm Bool
    ff  : Tm Bool
    ITE : {A : Ty} → Tm (A ⇒ A ⇒ Bool ⇒ A)
    Kβ  : {A B : Ty}{x : Tm A}{y : Tm B} → K $ x $ y ≡ x
    Sβ  : {A B C : Ty}{f : Tm (A ⇒ B ⇒ C)}{g : Tm (A ⇒ B)}{x : Tm A} → S $ f $ g $ x ≡ f $ x $ (g $ x)
    ttβ : {A : Ty}{x y : Tm A} → ITE $ x $ y $ tt ≡ x
    ffβ : {A : Ty}{x y : Tm A} → ITE $ x $ y $ ff ≡ y

-- Then we can define the general form of a Model and a Dependent Model

record DepModel {l} {l'} : Set (lsuc (l ⊔ l')) where
  infixr 5 _⇒•_
  infixl 5 _$•_
  open I
  
  field
    Ty•   : Ty → Set l
    ι•    : Ty• ι
    Bool• : Ty• Bool
    _⇒•_  : ∀{A B} → Ty• A → Ty• B → Ty• (A ⇒ B)
    Tm•   : ∀{A} → Ty• A → Tm A → Set l'
    _$•_  : ∀{A B}{A• : Ty• A}{B• : Ty• B}{u : Tm (A ⇒ B)}{v : Tm A} →
            Tm• (A• ⇒• B•) u → Tm• A• v  → Tm• B• (u $ v)
    K•    : ∀{A B}{A• : Ty• A}{B• : Ty• B} →
            Tm• (A• ⇒• B• ⇒• A•) K
    S•    : ∀{A B C}{A• : Ty• A}{B• : Ty• B}{C• : Ty• C} →
            Tm• ((A• ⇒• B• ⇒• C•) ⇒• (A• ⇒• B•) ⇒• A• ⇒• C•) S
    tt•   : Tm• Bool• tt
    ff•   : Tm• Bool• ff
    ITE•  : ∀{A}{A• : Ty• A} →
            Tm• (A• ⇒• A• ⇒• Bool• ⇒• A•) ITE
    Kβ•   : ∀{A B}{A• : Ty• A}{B• : Ty• B}{u : Tm A}{u• : Tm• A• u}{v : Tm B}{v• : Tm• B• v} →
            transp⟨ Tm• A• ⟩ Kβ (K• $• u• $• v•) ≡ u•
    Sβ•   : ∀{A B C}{A• : Ty• A}{B• : Ty• B}{C• : Ty• C}
             {f : Tm (A ⇒ B ⇒ C)}{f• : Tm• (A• ⇒• B• ⇒• C•) f}
             {g : Tm (A ⇒ B)}{g• : Tm• (A• ⇒• B•) g}
             {u : Tm A}{u• : Tm• A• u} →
            transp⟨ Tm• C• ⟩ Sβ (S• $• f• $• g• $• u•) ≡ f• $• u• $• (g• $• u•)
    ttβ•  : ∀{A}{A• : Ty• A}{u v : Tm A}{u• : Tm• A• u}{v• : Tm• A• v} →
            transp⟨ Tm• A• ⟩ ttβ (ITE• $• u• $• v• $• tt•) ≡ u•
    ffβ•  : ∀{A}{A• : Ty• A}{u v : Tm A}{u• : Tm• A• u}{v• : Tm• A• v} →
            transp⟨ Tm• A• ⟩ ffβ (ITE• $• u• $• v• $• ff•) ≡ v•

  indT : (A : Ty) → Ty• A
  indT ι       = ι•
  indT Bool    = Bool•
  indT (A ⇒ B) = (indT A) ⇒• (indT B)
    
  postulate
    ind    : ∀{A} → (u : Tm A) → Tm• (indT A) u
    ind$   : ∀{A B}{u : Tm (A ⇒ B)}{v : Tm A} →
             ind (u $ v) ≡ _$•_ {A} {B} {indT A} {indT B} {u} {v} (ind u) (ind v)
    indK   : ∀{A B} →
             ind (K {A} {B}) ≡ K• {A} {B} {indT A} {indT B}
    indS   : ∀{A B C} →
             ind (S {A} {B} {C}) ≡ S• {A} {B} {C} {indT A} {indT B} {indT C}
    indtt  : ind tt ≡ tt•
    indff  : ind ff ≡ ff•
    indITE : ∀{A} →
             ind (ITE {A}) ≡ ITE•
    {-# REWRITE ind$ indK indS indtt indff indITE #-}

-- then the model using the dependent model

record Model {l l'} : Set (lsuc (l ⊔ l')) where
  infixr 5 _⇒_
  infixl 5 _$_

  field
    Ty   : Set l
    ι    : Ty
    Bool : Ty
    _⇒_  : Ty → Ty → Ty
    Tm   : Ty → Set l'
    _$_  : ∀{A B}   → Tm (A ⇒ B) → Tm A → Tm B
    K    : ∀{A B}   → Tm (A ⇒ B ⇒ A)
    S    : ∀{A B C} → Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    tt   : Tm Bool
    ff   : Tm Bool
    ITE  : ∀{A} → Tm (A ⇒ A ⇒ Bool ⇒ A)
    Kβ   : ∀{A B}{u : Tm A}{v : Tm B} →
           K $ u $ v ≡ u
    Sβ   : ∀{A B C}{f : Tm (A ⇒ B ⇒ C)}{g : Tm (A ⇒ B)}{u : Tm A} →
           S $ f $ g $ u ≡ f $ u $ (g $ u)
    ttβ  : ∀{A}{u v : Tm A} →
           ITE $ u $ v $ tt ≡ u
    ffβ  : ∀{A}{u v : Tm A} →
           ITE $ u $ v $ ff ≡ v

  ModelRec : DepModel
  ModelRec = record
    { Ty•   = λ _ -> Ty
    ; ι•    = ι
    ; Bool• = Bool
    ; _⇒•_  = _⇒_
    ; Tm•   = λ A _ → Tm A
    ; _$•_  = _$_
    ; K•    = K
    ; S•    = S
    ; tt•   = tt
    ; ff•   = ff
    ; ITE•  = ITE
    ; Kβ•   = λ {A}{_}{_}{_}{u}{_}{v} → transpEq {_}{I.Tm A}{_}{_}{I.K I.$ u I.$ v}{u} Kβ
    ; Sβ•   = λ {_}{_}{C}{_}{_}{_}{u}{_}{v}{_}{x} → transpEq {_}{I.Tm C}{_}{_}{I.S I.$ u I.$ v I.$ x}{u I.$ x I.$ (v I.$ x)} Sβ
    ; ttβ•   = λ {A}{_}{u}{v} → transpEq {_}{I.Tm A}{_}{_}{I.ITE I.$ u I.$ v I.$ I.tt}{u} ttβ
    ; ffβ•   = λ {A}{_}{u}{v} → transpEq {_}{I.Tm A}{_}{_}{I.ITE I.$ u I.$ v I.$ I.ff}{v} ffβ
    }
  module ModelRec = DepModel ModelRec

  ⟦_⟧T : I.Ty → Ty
  ⟦_⟧T = ModelRec.indT

  ⟦_⟧ : ∀{A} → I.Tm A → Tm ⟦ A ⟧T
  ⟦_⟧ = ModelRec.ind

--------------------------------------------------

-- Then we have to describe the normal forms (model without equations)
-- Basically we can see them as all terms of SK where applications are all partials:

module _ where
  open I

  -- data isNf (A : Ty) : Tm A → Set

  data NF : I.Ty → Set where
    K₀   : ∀{A B} → NF (A ⇒ B ⇒ A)
    K₁   : ∀{A B} → NF A → NF (B ⇒ A)
    S₀   : ∀{A B C} → NF ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    S₁   : ∀{A B C} → NF (A ⇒ B ⇒ C) → NF ((A ⇒ B) ⇒ A ⇒ C)
    S₂   : ∀{A B C} → NF (A ⇒ B ⇒ C) → NF (A ⇒ B) → NF (A ⇒ C)
    TT   : NF Bool
    FF   : NF Bool
    ITE₀ : ∀{A} → NF (A ⇒ A ⇒ Bool ⇒ A)
    ITE₁ : ∀{A} → NF A → NF (A ⇒ Bool ⇒ A)
    ITE₂ : ∀{A} → NF A → NF A → NF (Bool ⇒ A)

  -- Then we can give the translations from a form to another :

  -- Inclusion

  ⌜_⌝ : ∀{A} → NF A → Tm A
  ⌜ K₀ ⌝ = K
  ⌜ K₁ u ⌝ = K $ ⌜ u ⌝
  ⌜ S₀ ⌝ = S
  ⌜ S₁ u ⌝ = S $ ⌜ u ⌝
  ⌜ S₂ u v ⌝ = S $ ⌜ u ⌝ $ ⌜ v ⌝
  ⌜ TT ⌝ = tt
  ⌜ FF ⌝ = ff
  ⌜ ITE₀ ⌝ = ITE
  ⌜ ITE₁ u ⌝ = ITE $ ⌜ u ⌝
  ⌜ ITE₂ u v ⌝ = ITE $ ⌜ u ⌝ $ ⌜ v ⌝

-- Normalisation

normBool : (u : I.Tm I.Bool) → Lift (u ≡ I.tt) ⨄ Lift (u ≡ I.ff) → NF I.Bool
normBool u (ι₁ _) = TT
normBool u (ι₂ _) = FF


NormProof : DepModel
NormProof = record
  { Ty•   = λ A → Σ (I.Tm A → Set) (λ RED → (u : I.Tm A) → RED u → NF A)
  ; ι•    = (λ _ → Lift ⊥) , λ _ p → ⊥-elim (unfold p) -- there is no term of type ι
  ; Bool• = (λ u → Lift (u ≡ I.tt) ⨄ Lift (u ≡ I.ff)) ,
            (λ u u• → normBool u u•)
  ; _⇒•_  = λ {A}{B} (REDA , _) (REDB , _) →
              (λ u → ((v : I.Tm A) → REDA v → REDB (u I.$ v)) × (NF (A I.⇒ B))) ,
              (λ _ u• → pr₂ u•)
  ; Tm•   = pr₁
  ; _$•_  = λ {_}{_}{_}{_}{_}{v} u• v• →
            (pr₁ u• v v•)
  ; K•    = λ {_}{_}{A•} →
            (λ u u• → (λ v v• → transp⟨ pr₁ A• ⟩ (symetry I.Kβ) u•) ,
                      K₁ (pr₂ A• u u•)) ,
            K₀
  ; S•    = λ {A}{B}{C}{A•}{B•}{C•} →
            (λ f f• →
              (λ g g• →
                (λ x x• → transp⟨ pr₁ C• ⟩ (symetry I.Sβ) (pr₁ (pr₁ f• x x•) (g I.$ x) (pr₁ g• x x• ))) ,
                (S₂ (pr₂ f•) (pr₂ g•))) ,
              (S₁ (pr₂ f•))) ,
            S₀
  ; tt•   = ι₁ ⟪ refl ⟫
  ; ff•   = ι₂ ⟪ refl ⟫
  ; ITE•  = λ {A}{A•} →
            (λ u u• →
              (λ v v• →
                (λ { b (ι₁ ⟪ e ⟫) → transp⟨ pr₁ A• ⟩ (symetry (transitivity (cong⟨ (λ x → (I.ITE I.$ u I.$ v I.$ x)) ⟩ e) I.ttβ)) u•
                   ; b (ι₂ ⟪ e ⟫) → transp⟨ pr₁ A• ⟩ (symetry (transitivity (cong⟨ (λ x → (I.ITE I.$ u I.$ v I.$ x)) ⟩ e) I.ffβ)) v• }) ,
                (ITE₂ (pr₂ A• u u•) (pr₂ A• v v•))) ,
              (ITE₁ (pr₂ A• u u•))) ,
            ITE₀
  ; Kβ•   = λ {_}{_}{A•} → transptransp (pr₁ A•) (symetry I.Kβ)
  ; Sβ•   = λ {_}{_}{_}{_}{_}{C•} → transptransp (pr₁ C•) (symetry I.Sβ){I.Sβ}
  ; ttβ•  = λ {_}{A•} → transptransp (pr₁ A•) (symetry I.ttβ)
  ; ffβ•  = λ {_}{A•} → transptransp (pr₁ A•) (symetry I.ffβ)
  }
module NormProof = DepModel NormProof

norm : ∀{A} → I.Tm A → NF A
norm {A} u = pr₂ (NormProof.indT A) u (NormProof.ind {A} u)

--------------------------------------------------

-- Homomorphism

-- in fact normalisation is a homomorphisme by defition

normK₀Morph : ∀{A}{B} → norm (I.K {A}{B}) ≡ (K₀ {A}{B})
normK₀Morph = refl

normK₁Morph : ∀{A}{B}{u : I.Tm A} → norm (I.K {A}{B} I.$ u) ≡ (K₁ {A}{B} (norm u))
normK₁Morph = refl -- rewrite (NormProof.ind$ {A}{B I.⇒ A}{I.K}{u}) = refl

normSMorph : ∀{A}{B}{C} → norm (I.S {A}{B}{C}) ≡ (S₀ {A}{B}{C})
normSMorph = refl

normS₁Morph : ∀{A}{B}{C}{f : I.Tm (A I.⇒ B I.⇒ C)} → norm (I.S I.$ f) ≡ S₁ (norm f)
normS₁Morph = refl

normS₂Morph : ∀{A}{B}{C}{f : I.Tm (A I.⇒ B I.⇒ C)}{g : I.Tm (A I.⇒ B)} → norm (I.S I.$ f I.$ g) ≡ S₂ (norm f) (norm g)
normS₂Morph = refl

-- inclusion is a homomorphism by definition

--------------------------------------------------

-- Completeness
-- we prove the completeness using a DepModel, exactly as the same way as normalisation

completenessBool : (u : I.Tm I.Bool) → Lift (u ≡ I.tt) ⨄ Lift (u ≡ I.ff) → ⌜ norm u ⌝ ≡ u
completenessBool u (ι₁ ⟪ refl ⟫) = refl
completenessBool u (ι₂ ⟪ refl ⟫) = refl

CompletenessProof : DepModel
CompletenessProof = record
  { Ty•  = λ A → Σ (I.Tm A → Set) (λ RED → (u : I.Tm A) → RED u → Lift (⌜ norm u ⌝ ≡ u))
  ; ι•   = (λ _ → Lift ⊥) , λ _ p → ⊥-elim (unfold p) -- there is no term of type ι
  ; Bool• = (λ u → Lift (u ≡ I.tt) ⨄ Lift (u ≡ I.ff)) ,
            (λ u u• → ⟪ completenessBool u u• ⟫)
  ; _⇒•_ = λ {A}{B} (REDA , _) (REDB , _) →
             (λ u → ((v : I.Tm A) → REDA v → REDB (u I.$ v)) × Lift (⌜ norm u ⌝ ≡ u)) ,
             (λ u u• → pr₂ u• )
  ; Tm•  = pr₁
  ; _$•_ = λ {_}{_}{_}{_}{_}{v} u• v• →
           (pr₁ u• v v•)
  ; K•   = λ {_}{_}{A•} →
           (λ u u• → (λ v v• → transp⟨ pr₁ A• ⟩ (symetry I.Kβ) u•) ,
                     ⟪ cong⟨ (λ x → I.K I.$ x) ⟩ (unfold (pr₂ A• u u•)) ⟫) ,
           ⟪ refl ⟫
  ; S•   = λ {A}{B}{C}{A•}{B•}{C•} →
           (λ f f• →
             (λ g g• →
               (λ x x• → transp⟨ pr₁ C• ⟩ (symetry I.Sβ) (pr₁ (pr₁ f• x x•) (g I.$ x) (pr₁ g• x x• ))) ,
               ⟪ I.S I.$ ⌜ norm f ⌝ I.$ ⌜ norm g ⌝ ≡⟨ cong⟨ (λ x → I.S I.$ ⌜ norm f ⌝ I.$ x) ⟩ (unfold (pr₂ g•)) ⟩
                 I.S I.$ ⌜ norm f ⌝ I.$      g     ≡⟨ cong⟨ (λ x → I.S I.$ x I.$ g) ⟩ (unfold (pr₂ f•)) ⟩
                     refl ⟫) ,
             ⟪ cong⟨ (λ x → I.S I.$ x) ⟩ (unfold (pr₂ f•)) ⟫) ,
           ⟪ refl ⟫
  ; tt•   = ι₁ ⟪ refl ⟫
  ; ff•   = ι₂ ⟪ refl ⟫
  ; ITE•  = λ {A}{A•} →
            (λ u u• →
              (λ v v• →
                (λ { b (ι₁ ⟪ e ⟫) → transp⟨ pr₁ A• ⟩ (symetry (transitivity (cong⟨ (λ x → (I.ITE I.$ u I.$ v I.$ x)) ⟩ e) I.ttβ)) u•
                   ; b (ι₂ ⟪ e ⟫) → transp⟨ pr₁ A• ⟩ (symetry (transitivity (cong⟨ (λ x → (I.ITE I.$ u I.$ v I.$ x)) ⟩ e) I.ffβ)) v• }) ,
                ⟪ I.ITE I.$ ⌜ norm u ⌝ I.$ ⌜ norm v ⌝ ≡⟨ cong⟨ (λ x → I.ITE I.$ ⌜ norm u ⌝ I.$ x) ⟩ (unfold (pr₂ A• v v•)) ⟩
                  I.ITE I.$ ⌜ norm u ⌝ I.$    v       ≡⟨ cong⟨ (λ x → I.ITE I.$ x I.$ v) ⟩ (unfold (pr₂ A• u u•)) ⟩
                     refl ⟫) ,
              ⟪ cong⟨ (λ x → I.ITE I.$ x) ⟩ (unfold (pr₂ A• u u•)) ⟫) ,
            ⟪ refl ⟫
  ; Kβ•  = λ {_}{_}{A•} → transptransp (pr₁ A•) (symetry I.Kβ)
  ; Sβ•  = λ {_}{_}{_}{_}{_}{C•} → transptransp (pr₁ C•) (symetry I.Sβ){I.Sβ}
  ; ttβ•  = λ {_}{A•} → transptransp (pr₁ A•) (symetry I.ttβ)
  ; ffβ•  = λ {_}{A•} → transptransp (pr₁ A•) (symetry I.ffβ)
  }
module CompletenessProof = DepModel CompletenessProof

completeness : ∀{A} → (u : I.Tm A) → ⌜ norm u ⌝ ≡ u
completeness {A} u =
  let A• = CompletenessProof.indT A in
  unfold (pr₂ A• u (CompletenessProof.ind {A} u))

--------------------------------------------------

-- Stability

-- normalisation stability

normStability : ∀{A} → (nf : NF A) → norm ⌜ nf ⌝ ≡ nf
normStability K₀         = refl
normStability (K₁ u)     = norm ⌜ K₁ u ⌝                 ≡⟨ refl ⟩
                           K₁ (norm ⌜ u ⌝)               ≡⟨ cong⟨ K₁ ⟩ (normStability u) ⟩
                           refl
normStability S₀         = refl
normStability (S₁ f)     = norm ⌜ S₁ f ⌝                 ≡⟨ refl ⟩
                           S₁ (norm ⌜ f ⌝)               ≡⟨ cong⟨ S₁ ⟩ (normStability f) ⟩
                           refl
normStability (S₂ f g)   = norm ⌜ S₂ f g ⌝               ≡⟨ refl ⟩
                           S₂ (norm ⌜ f ⌝) (norm ⌜ g ⌝)  ≡⟨ cong⟨ (λ x → S₂ x (norm ⌜ g ⌝)) ⟩ (normStability f) ⟩
                           S₂ f (norm ⌜ g ⌝)             ≡⟨ cong⟨ (S₂ f) ⟩ (normStability g) ⟩
                           refl
normStability TT         = refl
normStability FF         = refl
normStability ITE₀       = refl
normStability (ITE₁ u)   = norm ⌜ ITE₁ u ⌝               ≡⟨ refl ⟩
                           ITE₁ (norm ⌜ u ⌝)             ≡⟨ cong⟨ ITE₁ ⟩ (normStability u) ⟩
                           refl
normStability (ITE₂ u v) = norm ⌜ ITE₂ u v ⌝               ≡⟨ refl ⟩
                           ITE₂ (norm ⌜ u ⌝) (norm ⌜ v ⌝)  ≡⟨ cong⟨ (λ x → ITE₂ x (norm ⌜ v ⌝)) ⟩ (normStability u) ⟩
                           ITE₂ u (norm ⌜ v ⌝)             ≡⟨ cong⟨ (ITE₂ u) ⟩ (normStability v) ⟩
                           refl

--------------------------------------------------

-- Equality Decidability
-- Using normalisation we can prove that equality of terms is decidable

-- fisrt on types :

TyEqDec : (A : I.Ty ) → (B : I.Ty) → (A ≡ B) ∨ ¬ (A ≡ B)
TyEqDec  I.ι       I.ι        = left refl
TyEqDec  I.Bool    I.Bool     = left refl
TyEqDec (A I.⇒ B)  I.ι        = right (λ where ())
TyEqDec (A I.⇒ B)  I.Bool     = right (λ where ())
TyEqDec  I.ι      (A  I.⇒ B ) = right (λ where ())
TyEqDec  I.ι      I.Bool      = right (λ where ())
TyEqDec  I.Bool   (A  I.⇒ B ) = right (λ where ())
TyEqDec  I.Bool   I.ι         = right (λ where ())
TyEqDec (A I.⇒ B) (A' I.⇒ B') with TyEqDec A A' | TyEqDec B B'
... | left refl  | left refl  = left refl
... | right A≠A' | _          = right (λ {refl → A≠A' refl})
... | _          | right B≠B' = right (λ {refl → B≠B' refl})

-- then on normal forms ...
-- there is 100 cases ??!

NfEqDec : ∀{A} → (u : NF A) → (v : NF A) → (u ≡ v) ∨ ¬ (u ≡ v)
NfEqDec (K₀) (K₁ _)         = right (λ where ())
NfEqDec (K₀) (S₁ _)         = right (λ where ())
NfEqDec (K₀) (S₂ _ _)       = right (λ where ())
NfEqDec (K₀) (ITE₁ _)       = right (λ where ())
NfEqDec (K₀) (ITE₂ _ _)     = right (λ where ())
NfEqDec (K₁ _) (K₀)         = right (λ where ())
NfEqDec (K₁ _) (S₀)         = right (λ where ())
NfEqDec (K₁ _) (S₁ _)       = right (λ where ())
NfEqDec (K₁ _) (S₂ _ _)     = right (λ where ())
NfEqDec (K₁ _) (ITE₀)       = right (λ where ())
NfEqDec (K₁ _) (ITE₁ _)     = right (λ where ())
NfEqDec (K₁ _) (ITE₂ _ _)   = right (λ where ())
NfEqDec (S₀) (S₂ _ _)       = right (λ where ())
NfEqDec (S₀) (K₁ _)         = right (λ where ())
NfEqDec (S₁ _) (S₂ _ _)     = right (λ where ())
NfEqDec (S₁ _) (K₀)         = right (λ where ())
NfEqDec (S₁ _) (K₁ _)       = right (λ where ())
NfEqDec (S₁ _) (ITE₁ _)     = right (λ where ())
NfEqDec (S₂ _ _) (S₀)       = right (λ where ())
NfEqDec (S₂ _ _) (S₁ _)     = right (λ where ())
NfEqDec (S₂ _ _) (K₀)       = right (λ where ())
NfEqDec (S₂ _ _) (K₁ _)     = right (λ where ())
NfEqDec (S₂ _ _) (ITE₀)     = right (λ where ())
NfEqDec (S₂ _ _) (ITE₁ _)   = right (λ where ())
NfEqDec (S₂ _ _) (ITE₂ _ _) = right (λ where ())
NfEqDec (K₀) (K₀)         = left refl
NfEqDec (K₁ u) (K₁ u') with NfEqDec u u'
...        | left refl  = left refl
...        | right u≠u' = right (λ {refl → u≠u' refl})
NfEqDec (S₀) (S₀)       = left refl
NfEqDec (S₁ u) (S₁ u') with NfEqDec u u'
...        | left refl  = left refl
...        | right u≠u' = right (λ {refl → u≠u' refl})
NfEqDec (S₂ {_}{B}{_} u v) (S₂ {_}{B'}{_} u' v') with TyEqDec B B'
...                                              | left refl with NfEqDec u u' | NfEqDec v v'
...                                                             | left refl  | left refl   = left refl
...                                                             | right u≠u' | _          = right (λ {refl → u≠u' refl}) 
...                                                             | _          | right v≠v' = right (λ {refl → v≠v' refl})   
NfEqDec (S₂ {_}{B}{_} u v) (S₂ {_}{B'}{_} u' v') | right B≠B' = right (λ {refl → B≠B' refl})

-- and finaly on terms :

TmEqDec : ∀{A}{u : I.Tm A}{v : I.Tm A} → (u ≡ v) ∨ ¬ (u ≡ v)
TmEqDec {A}{u}{v} with NfEqDec (norm u) (norm v)
...                     | left  nu=nv = left (u          ≡⟨ symetry (completeness u) ⟩
                                              ⌜ norm u ⌝ ≡⟨ cong⟨ ⌜_⌝ ⟩ nu=nv ⟩
                                              ⌜ norm v ⌝ ≡⟨ completeness v ⟩
                                              refl )
...                     | right nu≠nv = right (λ {refl → nu≠nv refl})

\end{code}
 
--------------------------------------------------
