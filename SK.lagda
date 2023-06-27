\begin{code}

{-# OPTIONS --prop --rewriting #-}

open import Agda.Primitive
open import Equality
open import Logic
open import Nat

module SK where

--------------------------------------------------

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
    ind  : ∀{A} → (u : I.Tm A) → Tm• (indT A) u
    ind$ : ∀{A B}{u : I.Tm (A I.⇒ B)}{v : I.Tm A} →
           ind (u I.$ v) ≡ _$•_ {A} {B} {indT A} {indT B} {u} {v} (ind u) (ind v)
    indK : ∀{A B} →
           ind (I.K {A} {B}) ≡ K• {A} {B} {indT A} {indT B}
    indS : ∀{A B C} →
           ind (I.S {A} {B} {C}) ≡ S• {A} {B} {C} {indT A} {indT B} {indT C}
    {-# REWRITE ind$ indK indS #-}

-- then the model using the dependent model

record Model {l l'} : Set (lsuc (l ⊔ l')) where
  infixr 5 _⇒_
  infixl 5 _$_

  field
    Ty  : Set l
    ι   : Ty
    _⇒_ : Ty → Ty → Ty
    Tm  : Ty → Set l'
    _$_ : ∀{A B}   → Tm (A ⇒ B) → Tm A → Tm B
    K   : ∀{A B}   → Tm (A ⇒ B ⇒ A)
    S   : ∀{A B C} → Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    Kβ  : ∀{A B}{u : Tm A}{v : Tm B} →
          K $ u $ v ≡ u
    Sβ  : ∀{A B C}{f : Tm (A ⇒ B ⇒ C)}{g : Tm (A ⇒ B)}{u : Tm A} →
          S $ f $ g $ u ≡ f $ u $ (g $ u)

  ModelRec : DepModel
  ModelRec = record
    { Ty•  = λ _ -> Ty
    ; ι•   = ι
    ; _⇒•_ = _⇒_
    ; Tm•  = λ A _ → Tm A
    ; _$•_ = _$_
    ; K•   = K
    ; S•   = S
    ; Kβ•  = λ {A}{_}{_}{_}{u}{_}{v} → transpEq {_}{I.Tm A}{_}{_}{I.K I.$ u I.$ v}{u} Kβ
    ; Sβ•  = λ {_}{_}{C}{_}{_}{_}{u}{_}{v}{_}{x} → transpEq {_}{I.Tm C}{_}{_}{I.S I.$ u I.$ v I.$ x}{u I.$ x I.$ (v I.$ x)} Sβ
    }
  module ModelRec = DepModel ModelRec

  ⟦_⟧T : I.Ty → Ty
  ⟦_⟧T = ModelRec.indT

  ⟦_⟧ : ∀{A} → I.Tm A → Tm ⟦ A ⟧T
  ⟦_⟧ = ModelRec.ind

-- or even a model where only type is dependant :

record TypeDepModel {l} {l'} : Set (lsuc (l ⊔ l')) where
  infixr 5 _⇒•_
  infixl 5 _$_

  field
    Ty•  : I.Ty → Set l
    ι•   : Ty• I.ι
    _⇒•_ : ∀{A B} → Ty• A → Ty• B → Ty• (A I.⇒ B)
    Tm   : ∀{A} → Ty• A → Set l'
    _$_  : ∀{A B}{A• : Ty• A}{B• : Ty• B} →
           Tm (A• ⇒• B•) → Tm A•  → Tm B•
    K    : ∀{A B}{A• : Ty• A}{B• : Ty• B} →
           Tm (A• ⇒• B• ⇒• A•)
    S    : ∀{A B C}{A• : Ty• A}{B• : Ty• B}{C• : Ty• C} →
           Tm ((A• ⇒• B• ⇒• C•) ⇒• (A• ⇒• B•) ⇒• A• ⇒• C•)
    Kβ   : ∀{A B}{A• : Ty• A}{B• : Ty• B}{u : Tm A•}{v : Tm B•} →
           (K $ u $ v) ≡ u
    Sβ   : ∀{A B C}{A• : Ty• A}{B• : Ty• B}{C• : Ty• C}
            {f : Tm (A• ⇒• B• ⇒• C•)}{g : Tm (A• ⇒• B•)}{u : Tm A•} →
            (S $ f $ g $ u) ≡ f $ u $ (g $ u)

  ModelRec : DepModel
  ModelRec = record
    { Ty•  = Ty•
    ; ι•   = ι•
    ; _⇒•_ = _⇒•_
    ; Tm•  = λ A• _ → Tm A•
    ; _$•_ = _$_
    ; K•   = K
    ; S•   = S
    ; Kβ•  = λ {A}{_}{_}{_}{u}{_}{v} → transpEq {_}{I.Tm A}{_}{_}{I.K I.$ u I.$ v}{u} Kβ
    ; Sβ•  = λ {_}{_}{C}{_}{_}{_}{u}{_}{v}{_}{x} → transpEq {_}{I.Tm C}{_}{_}{I.S I.$ u I.$ v I.$ x}{u I.$ x I.$ (v I.$ x)} Sβ
    }
  module ModelRec = DepModel ModelRec

  indT : (A : I.Ty) → Ty• A
  indT = ModelRec.indT

  ⟦_⟧ : ∀{A} → I.Tm A → Tm (indT A)
  ⟦_⟧ = ModelRec.ind
  

--------------------------------------------------

-- this is possible to convert any DepModel / HalfDepModel to a Model :

TypeDepModelToModel : ∀{l}{l'} → TypeDepModel {l}{l'} → Model {l} {l'}
TypeDepModelToModel M =
  let module M = TypeDepModel M in record
  { Ty  = Σ I.Ty (λ A → M.Ty• A)
  ; ι   = I.ι , M.ι•
  ; _⇒_ = λ {(A , A•) (B , B•) → (A I.⇒ B) , (A• M.⇒• B•)}
  ; Tm  = λ {(A , A•) → M.Tm A•}
  ; _$_ = λ u v → u M.$ v
  ; K   = M.K
  ; S   = M.S
  ; Kβ  = M.Kβ
  ; Sβ  = M.Sβ
  }

DepModelToModel : ∀{l}{l'} → DepModel {l}{l'} → Model {l}{l'}
DepModelToModel M =
  let module M = DepModel M in record
  { Ty  = Σ I.Ty (λ A → M.Ty• A)
  ; ι   = I.ι , M.ι•
  ; _⇒_ = λ {(A , A•) (B , B•) → (A I.⇒ B) , (A• M.⇒• B•)}
  ; Tm  = λ {(A , A•) → Σ (I.Tm A) (λ t → M.Tm• A• t)}
  ; _$_ = λ {(u , u•) (v , v•) → (u I.$ v) , (u• M.$• v•)}
  ; K   = I.K , M.K•
  ; S   = I.S , M.S•
  ; Kβ  = transpΣ I.Kβ M.Kβ•
  ; Sβ  = transpΣ I.Sβ M.Sβ•
  }

--------------------------------------------------

-- Then we have to describe the normal forms (model without equations)
-- Basically we can see them as all terms of SK where applications are all partials:

module _ where
  open I

  -- data isNf (A : Ty) : Tm A → Set

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
  { Ty•  = λ A → Σ (I.Tm A → Set) (λ RED → {u : I.Tm A} → RED u → NF A)
  ; ι•   = (λ _ → Lift ⊥) , λ p → ⊥-elim (unfold p) -- there is no term of type ι
  ; _⇒•_ = λ {A}{B} (REDA , _) (REDB , _) →
             (λ u → ({v : I.Tm A} → REDA v → REDB (u I.$ v)) × (NF (A I.⇒ B))) ,
             (λ u• → pr₂ u•)
  ; Tm•  = pr₁
  ; _$•_ = λ {_}{_}{_}{_}{_}{v} u• v• →
           (pr₁ u• v•)
  ; K•   = λ {_}{_}{A•} →
           (λ u• → (λ v• → transp⟨ pr₁ A• ⟩ (symetry I.Kβ) u•) ,
                     K₁ (pr₂ A• u•)) ,
           K₀
  ; S•   = λ {A}{B}{C}{A•}{B•}{C•} →
           (λ {f} f• →
             (λ {g} g• →
               (λ x• → transp⟨ pr₁ C• ⟩ (symetry I.Sβ) (pr₁ (pr₁ f• x•) (pr₁ g• x• ))) ,
               (S₂ (pr₂ f•) (pr₂ g•))) ,
             (S₁ (pr₂ f•))) ,
           S₀
  ; Kβ•  = λ {_}{_}{A•} → transptransp (pr₁ A•) (symetry I.Kβ)
  ; Sβ•  = λ {_}{_}{_}{_}{_}{C•} → transptransp (pr₁ C•) (symetry I.Sβ){I.Sβ}
  }
module NormProof = DepModel NormProof

norm : ∀{A} → I.Tm A → NF A
norm {A} u = pr₂ (NormProof.indT A) (NormProof.ind {A} u)

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

CompletenessProof : DepModel
CompletenessProof = record
  { Ty•  = λ A → Σ (I.Tm A → Set) (λ RED → (u : I.Tm A) → RED u → Lift (⌜ norm u ⌝ ≡ u))
  ; ι•   = (λ _ → Lift ⊥) , λ _ p → ⊥-elim (unfold p) -- there is no term of type ι
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
                     I.S I.$ ⌜ norm f ⌝ I.$    g     ≡⟨ cong⟨ (λ x → I.S I.$ x I.$ g) ⟩ (unfold (pr₂ f•)) ⟩
                     refl ⟫) ,
             ⟪ cong⟨ (λ x → I.S I.$ x) ⟩ (unfold (pr₂ f•)) ⟫) ,
           ⟪ refl ⟫
  ; Kβ•  = λ {_}{_}{A•} → transptransp (pr₁ A•) (symetry I.Kβ)
  ; Sβ•  = λ {_}{_}{_}{_}{_}{C•} → transptransp (pr₁ C•) (symetry I.Sβ){I.Sβ}
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
normStability K₀       = refl
normStability (K₁ u)   = norm ⌜ K₁ u ⌝                 ≡⟨ normK₁Morph ⟩
                         K₁ (norm ⌜ u ⌝)               ≡⟨ cong⟨ K₁ ⟩ (normStability u) ⟩
                         refl
normStability S₀       = refl
normStability (S₁ f)   = norm ⌜ S₁ f ⌝                 ≡⟨ refl ⟩
                         S₁ (norm ⌜ f ⌝)               ≡⟨ cong⟨ S₁ ⟩ (normStability f) ⟩
                         refl
normStability (S₂ f g) = norm ⌜ S₂ f g ⌝               ≡⟨ refl ⟩
                         S₂ (norm ⌜ f ⌝) (norm ⌜ g ⌝)  ≡⟨ cong⟨ (λ x → S₂ x (norm ⌜ g ⌝)) ⟩ (normStability f) ⟩
                         S₂ f (norm ⌜ g ⌝)             ≡⟨ cong⟨ (S₂ f) ⟩ (normStability g) ⟩
                         refl

--------------------------------------------------

-- Equality Decidability
-- Using normalisation we can prove that equality of terms is decidable

-- fisrt on types :

TyEqDec : (A : I.Ty ) → (B : I.Ty) → (A ≡ B) ∨ ¬ (A ≡ B)
TyEqDec  I.ι       I.ι        = left refl
TyEqDec (A I.⇒ B)  I.ι        = right (λ where ())
TyEqDec  I.ι      (A  I.⇒ B ) = right (λ where ())
TyEqDec (A I.⇒ B) (A' I.⇒ B') with TyEqDec A A' | TyEqDec B B'
... | left refl  | left refl  = left refl
... | right A≠A' | _          = right (λ {refl → A≠A' refl})
... | _          | right B≠B' = right (λ {refl → B≠B' refl})

-- then on normal forms ...

NfEqDec : ∀{A} → (u v : NF A) → (u ≡ v) ∨ ¬ (u ≡ v)
NfEqDec (K₀) (K₁ _)     = right (λ ())
NfEqDec (K₀) (S₁ _)     = right (λ ())
NfEqDec (K₀) (S₂ _ _)   = right (λ ())
NfEqDec (K₁ _) (K₀)     = right (λ ())
NfEqDec (K₁ _) (S₀)     = right (λ ())
NfEqDec (K₁ _) (S₁ _)   = right (λ ())
NfEqDec (K₁ _) (S₂ _ _) = right (λ ())
NfEqDec (S₀) (S₂ _ _)   = right (λ ())
NfEqDec (S₀) (K₁ _)     = right (λ ())
NfEqDec (S₁ _) (S₂ _ _) = right (λ ())
NfEqDec (S₁ _) (K₀)     = right (λ ())
NfEqDec (S₁ _) (K₁ _)   = right (λ ())
NfEqDec (S₂ _ _) (S₀)   = right (λ ())
NfEqDec (S₂ _ _) (S₁ _) = right (λ ())
NfEqDec (S₂ _ _) (K₀)   = right (λ ())
NfEqDec (S₂ _ _) (K₁ _) = right (λ ())
NfEqDec (K₀) (K₀)       = left refl
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

\end{code}

-- Maybe it could be easier with :

Nf_to_LBT : ∀{A} → NF A → LBT
Nf_to_LBT K₀ = Leaf 𝟘
Nf_to_LBT (K₁ u) = Node (Leaf 𝟙) (Nf_to_LBT u)
Nf_to_LBT S₀ = Leaf 𝟚
Nf_to_LBT (S₁ u) = Node (Leaf 𝟛) (Nf_to_LBT u)
Nf_to_LBT (S₂ u v) = Node (Leaf 𝟜) (Node (Nf_to_LBT u) (Nf_to_LBT v))

-- Then decoding function
postulate LBT_to_Nf : ∀{A} → LBT → NF A

-- then injectivity using :
postulate stableEncode : ∀{A} → (u : NF A) → LBT_to_NF (Nf_to_LBT u) ≡ u
-- but this is false, encoding need to encode types...

Inject : ∀{A} → (u v : NF A) → (Nf_to_LBT u) ≡ (Nf_to_LBT v) → u ≡ v
Inject u v e = u                       ≡⟨ symetry (stableEncode u) ⟩
               LBT_to_NF (Nf_to_LBT u) ≡⟨ cong⟨ LBT_to_Nf ⟩ e ⟩
               LBT_to_NF (Nf_to_LBT v) ≡⟨ stableEncode v ⟩
               v

NfEqDec : ∀{A} → (u v : NF A) → (u ≡ v) ∨ ¬ (u ≡ v)
NfEqDec u v with LBTDecEq (Nf_to_LBT u) (Nf_to_LBT v)
... | left e = left (Inject u v e)
... | right tu≠tv = right (λ {refl → tu≠tv refl})

\begin{code}

-- and finaly on terms :

TmEqDec : ∀{A}{u : I.Tm A}{v : I.Tm A} → (u ≡ v) ∨ ¬ (u ≡ v)
TmEqDec {A}{u}{v} with NfEqDec (norm u) (norm v)
...                     | left  nu=nv = left (u          ≡⟨ symetry (completeness u) ⟩
                                              ⌜ norm u ⌝ ≡⟨ cong⟨ ⌜_⌝ ⟩ nu=nv ⟩
                                              ⌜ norm v ⌝ ≡⟨ completeness v ⟩
                                              refl )
...                     | right nu≠nv = right (λ {refl → nu≠nv refl})

--------------------------------------------------

-- An other version of normalisation

Norm : TypeDepModel
Norm = record
  { Ty•  = λ A → Σ Set (λ Ap → (Ap → NF A))
  ; ι•   = ∅ , λ () -- there is no term of type ι
  ; _⇒•_ = λ {A}{B} (Ap , qA) (Bp , qB) →
             Σ (NF (A I.⇒ B)) (λ t → Σ (Ap → Bp) (λ f → Lift ((⌜_⌝) ∘ qB ∘ f ≡ (⌜ t ⌝ I.$_) ∘ (⌜_⌝) ∘ qA))) , pr₁
  ; Tm   = λ {A} (Ap , qA) → Ap
  ; _$_  = λ {A}{B}{(Ap , qA)}{(Bp , qB)} u v →
           let f = pr₁ (pr₂ u) in
           f v
  ; K    = λ {A}{B}{(Ap , qA)}{(Bp , qB)} →
           K₀ ,
           (((λ αu → K₁ (qA αu) ,
                     ((λ αv → αu) ,
                     ⟪ funext (λ α → symetry I.Kβ) ⟫)) ,
           ⟪ refl ⟫))
  ; S     = λ {A}{B}{C}{(Ap , qA)}{(Bp , qB)}{(Cp , qC)} →
            S₀ ,
            ((λ αf → S₁ (pr₁ αf) ,
                     ((λ αg → S₂ (pr₁ αf) (pr₁ αg) ,
                              ((λ αx → ((pr₁ (pr₂ ((pr₁ (pr₂ αf)) αx)))) ((pr₁ (pr₂ αg)) αx)) ,
                              ⟪ funext (λ α → let fAB = pr₁ (pr₂ αg) in
                                              let fBC = pr₁ (pr₂ ((pr₁ (pr₂ αf)) α)) in -- ?
                                              let fAB' = ⌜ pr₁ αg ⌝ I.$_ in
                                              let fBC' = ⌜ pr₁ ((pr₁ (pr₂ αf)) α) ⌝ I.$_ in -- ?
                                              let fABdiag = unfold (pr₂ (pr₂ αg)) in
                                              let fBCdiag = unfold (pr₂ (pr₂ ((pr₁ (pr₂ αf)) α))) in -- ?
                                              let fACdiag = concatdiag fAB fBC (⌜_⌝ ∘ qA) (⌜_⌝ ∘ qB) (⌜_⌝ ∘ qC) fAB' fBC' fABdiag fBCdiag in
                                              ⌜ qC (fBC (fAB α)) ⌝   ≡⟨ cong⟨ (λ x → x α) ⟩ fACdiag ⟩
                                               fBC' (fAB' ⌜ qA α ⌝)  ≡⟨ cong⟨ (λ x → (x α) I.$ (fAB' ⌜ qA α ⌝)) ⟩ (unfold (pr₂ (pr₂ αf))) ⟩
                                               symetry I.Sβ) ⟫)) ,
                     ⟪ funext (λ α → refl) ⟫)) ,
            ⟪ refl ⟫)
  ; Kβ   = refl
  ; Sβ   = refl
  }
module Norm = TypeDepModel Norm

norm' : ∀{A} → I.Tm A → NF A
norm' {A} u =  (pr₂ (Norm.indT A)) Norm.⟦ u ⟧

Comp : DepModel
Comp = record
  { Ty•  = λ A → I.Ty
  ; ι•   = I.ι
  ; _⇒•_ = I._⇒_
  ; Tm•  = λ {A} A• t →  Lift (⌜ norm' t ⌝ ≡ t)
  ; _$•_ = λ {A}{B}{_}{_}{u}{v} u• v• →
           let (Ap , qA) = Norm.indT A in
           let (Bp , qB) = Norm.indT B in 
           let f = pr₁ (pr₂ Norm.⟦ u ⟧) in
           let fdiag = unfold (pr₂ (pr₂ Norm.⟦ u ⟧)) in
           ⟪ ⌜ qB (f Norm.⟦ v ⟧) ⌝ ≡⟨ cong⟨ (λ x → x Norm.⟦ v ⟧) ⟩ fdiag ⟩
             ⌜ norm' u ⌝ I.$ ⌜ norm' v ⌝ ≡⟨ cong⟨ (λ x → ⌜ norm' u ⌝ I.$ x) ⟩ (unfold v•) ⟩
             ⌜ norm' u ⌝ I.$ v ≡⟨ cong⟨ (λ x → x I.$ v) ⟩ (unfold u•) ⟩
             refl
           ⟫
  ; K•   = ⟪ refl ⟫
  ; S•   = ⟪ refl ⟫
  ; Kβ•  = refl
  ; Sβ•  = refl
  }
module Comp = DepModel Comp

comp' : ∀{A} → (u : I.Tm A) → ⌜ norm' u ⌝ ≡ u
comp' u = unfold (Comp.ind u)

norm'Stability : ∀{A} → (nf : NF A) → norm' ⌜ nf ⌝ ≡ nf
norm'Stability K₀       = refl
norm'Stability (K₁ u)   = cong⟨ K₁ ⟩ (norm'Stability u)
norm'Stability S₀       = refl
norm'Stability (S₁ f)   = cong⟨ S₁ ⟩ (norm'Stability f)
norm'Stability (S₂ f g) = S₂ (norm' ⌜ f ⌝) (norm' ⌜ g ⌝)  ≡⟨ cong⟨ (λ x → S₂ x (norm' ⌜ g ⌝)) ⟩ (norm'Stability f) ⟩
                          S₂ f (norm' ⌜ g ⌝)             ≡⟨ cong⟨ (S₂ f) ⟩ (norm'Stability g) ⟩
                          refl

---------------------------------------------

-- but this time we can show that the Normalisation Model is a strict syntax
-- (a model isomorphic to the syntax where equality are definitional)

module NM = Model (TypeDepModelToModel Norm)

-- we can check that the equalities are in fact definitional :

Kβ-NM : {A B : NM.Ty} {u : NM.Tm A} {v : NM.Tm B} → NM._$_ {_} {A} (NM._$_ {A} {B NM.⇒ A} NM.K u) v ≡ u
Kβ-NM = refl

Sβ-NM : {A B C : NM.Ty} {u : NM.Tm (A NM.⇒ B NM.⇒ C)} {v : NM.Tm (A NM.⇒ B)} {x : NM.Tm A} →
        NM._$_ {_}{C} (NM._$_ {_}{A NM.⇒ C} (NM._$_ {A NM.⇒ B NM.⇒ C}{(A NM.⇒ B) NM.⇒ A NM.⇒ C} (NM.S {A}{B}{C}) u) v) x
        ≡ (NM._$_ {B} {C} (NM._$_ {A} {B NM.⇒ C} u x) (NM._$_ {A} {B} v x))
Sβ-NM = refl

-- then make the isomorphism between Syntax (I) and the Normalisation Model (NM)

-- one way is juste the eleminator on the dependant model :

fT : I.Ty → NM.Ty
fT = NM.⟦_⟧T
f : ∀{A} → I.Tm A → NM.Tm (fT A)
f = NM.⟦_⟧

-- this, by definition an homomorphism so we don't show it (just refl for all equations)

-- the other way is obtained by translation of the normal form to a syntactic form :

gT : NM.Ty → I.Ty
gT = pr₁
g : ∀{A} → NM.Tm A → I.Tm (gT A)
g {A} u = ⌜ (pr₂ (pr₂ A)) u ⌝

-- we have to show that this is a homomorphism
-- the only tricky part is for application ($)

gTmorphι : gT NM.ι ≡ I.ι
gTmorphι = refl

gTmorph⇒ : ∀{A}{B} → gT (A NM.⇒ B) ≡ (gT A) I.⇒ (gT B)
gTmorph⇒ = refl

gmorph$ : {A B : NM.Ty}{u : NM.Tm (A NM.⇒ B)}{v : NM.Tm A} →
          g {B} (NM._$_ {_}{B} u v) ≡ (g {A NM.⇒ B} u) I.$ (g {A} v)
gmorph$ {A}{B}{u}{v} = cong⟨ (λ x → x v) ⟩ (unfold (pr₂ (pr₂ u)))

gmorphK : ∀{A}{B} → g {A NM.⇒ B NM.⇒ A} (NM.K {A}{B}) ≡ I.K
gmorphK = refl

gmorphS : ∀{A}{B}{C} → g {(A NM.⇒ B NM.⇒ C) NM.⇒ (A NM.⇒ B) NM.⇒ A NM.⇒ C}
                         (NM.S {A}{B}{C}) ≡ I.S {gT A}{gT B}{gT C}
gmorphS = refl 

-- then we have to prove that the models are isomorphic
-- it mean that fT ∘ gT = id / gT ∘ fT = id
--         and  f  ∘ g  = id / g  ∘ f  = id

-- because fT and gT are homomoprhism, gT ∘ fT is one too, but there is only one endomorpism on the syntax (which is id)
-- so we do not have to prove that "gT ∘ fT = id"
-- and similary we do not have to prove that "g ∘ f = id"

-- then the other way :

-- but actually the other way is NOT true, NM.Ty is too large and contains too much informations as shown :

ι' : NM.Ty
ι' = (I.ι , Lift (⊥) , λ ())
-- NM.ι = (I.ι , ∅ , λ ())
test : fT (gT ι') ≡ NM.ι
test = refl

-- in fact (Ap : Set) × (qA : Ap → NF A) should be propositional (𝟙 type) maybe we have to add equations ?

\end{code}


