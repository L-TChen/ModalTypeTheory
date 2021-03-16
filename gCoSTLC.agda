{-# OPTIONS --cubical #-}

-- Guarded infinitary simply typed λ-Calculus with products

module gCoSTLC where

open import Data.Nat
  hiding (_≟_)

open import Later

pure  = next_
_<*>_ = _⊛_

import STLC as S
open S._⊢_

open import Context        public
  hiding ([_])

infix  3 _⊢_ _⊢_-→_ _⊢_-↠_ _⊢_-↠ᵍ_

infix  0 begin_
infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_
infix  3 _∎

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixr 6 proj₁_ proj₂_
infixl 7 _·_
infixl 8 _[_] _⟪_⟫
infix  9 `_ #_

data _⊢_ (Γ : Cxt) : Type → Set

private
  variable
    Γ Γ′           : Cxt
    A B            : Type
    M N L M′ N′ L′ : Γ ⊢ A

------------------------------------------------------------------------------
-- Typing Rules

data _⊢_ Γ where
  undefined : Γ ⊢ A
  
  `_
    : Γ ∋ A
      ---------
    → Γ ⊢ A
  ƛ_
    : ▹ (Γ , A ⊢ B)
      ----------------
    → Γ     ⊢ A →̇ B
  _·_
    : ▹ (Γ ⊢ A →̇ B)
    → ▹ (Γ ⊢ A)
      ----------
    → Γ ⊢ B
  ⟨⟩
    : Γ ⊢ ⊤̇ 
  ⟨_,_⟩
    : ▹ (Γ ⊢ A)
    → ▹ (Γ ⊢ B)
    → Γ ⊢ A ×̇ B
  proj₁_
    : ▹ (Γ ⊢ A ×̇ B)
    → Γ ⊢ A
  proj₂_
    : ▹ (Γ ⊢ A ×̇ B)
    → Γ ⊢ B

#_ : (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Injection from STLC to guarded STLC

fromSTLC
  : Γ S.⊢ A
  → Γ   ⊢ A
fromSTLC (` x)     = ` x
fromSTLC (ƛ M)     = ƛ next (fromSTLC M)
fromSTLC (M · N)   = next fromSTLC M · next fromSTLC N
fromSTLC ⟨⟩        = ⟨⟩
fromSTLC ⟨ M , N ⟩ = ⟨ next fromSTLC M , next fromSTLC N ⟩
fromSTLC (proj₁ L) = proj₁ next fromSTLC L
fromSTLC (proj₂ L) = proj₂ next fromSTLC L

------------------------------------------------------------------------------
-- Variable renaming

rename : Rename Γ Γ′
  → Γ  ⊢ A
  → Γ′ ⊢ A
rename = fix {A = ∀ {A Γ Γ′} → Rename Γ Γ′ → Γ ⊢ A → Γ′ ⊢ A} λ rename▹ ρ → λ where
  undefined → undefined
  (` x)     → ` ρ x
  (ƛ M)     → ƛ λ α → rename▹ α (ext ρ) (M α)
  (M · N)   → (λ α → rename▹ α ρ (M α)) · λ α → rename▹ α ρ (N α)
  ⟨⟩        → ⟨⟩
  ⟨ M , N ⟩ → ⟨ (λ α → rename▹ α ρ (M α)) , (λ α → rename▹ α ρ (N α)) ⟩
  (proj₁ L) → proj₁ λ α → rename▹ α ρ (L α)
  (proj₂ L) → proj₂ λ α → rename▹ α ρ (L α) 

wk
  : Γ ⊢ A
  → Γ , B ⊢ A
wk = rename S_

------------------------------------------------------------------------------
-- Substitution

Subst
  : Cxt → Cxt → Set
Subst Γ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ⊢ A

exts
  : Subst Γ Γ′
  → Subst (Γ , B) (Γ′ , B)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

_⟪_⟫
  : Γ  ⊢ A
  → Subst Γ Γ′
  → Γ′ ⊢ A
_⟪_⟫ = fix {A = ∀ {A Γ Γ′} → Γ ⊢ A → Subst Γ Γ′ → Γ′ ⊢ A} λ subst▹ → λ where
  undefined _ → undefined
  (` x)     σ → σ x
  (ƛ M)     σ → ƛ λ α → subst▹ α (M α) (exts σ)
  (M · N)   σ → (λ α → subst▹ α (M α) σ) · λ α → subst▹ α (N α) σ
  ⟨⟩        σ → ⟨⟩
  ⟨ M , N ⟩ σ → ⟨ (λ α → subst▹ α (M α) σ) , (λ α → subst▹ α (N α) σ) ⟩
  (proj₁ L) σ → proj₁ λ α → subst▹ α (L α) σ 
  (proj₂ L) σ → proj₂ λ α → subst▹ α (L α) σ

subst-zero
  : Γ ⊢ B
  → Subst (Γ , B) Γ
subst-zero N Z     = N
subst-zero N (S x) = ` x

_[_]
  : Γ , B ⊢ A
  → Γ ⊢ B
  → Γ ⊢ A
M [ N ] = M ⟪ subst-zero N ⟫

------------------------------------------------------------------------------
-- Examples 

L=⟨L₁,L₂⟩ : ∅ ⊢ A ×̇ B
L=⟨L₁,L₂⟩ = fix λ L▹ →
  ⟨ next (proj₁ L▹)  , next (proj₂ L▹) ⟩

μ_ : Γ , A ⊢ A
   → Γ ⊢ A
μ M = fix λ Y▹ → next (ƛ next M) · Y▹

------------------------------------------------------------------------------
-- Single-step reduction

data _⊢_-→_ (Γ : Cxt) : (M N : Γ ⊢ A) → Set where
  β-ƛ·
    : Γ ⊢ next (ƛ next M) · (next N) -→ M [ N ]

  β-⟨,⟩proj₁
    : {N : ▹ (Γ ⊢ B)}
    → Γ ⊢ proj₁ (next ⟨ next M , N ⟩) -→ M

  β-⟨,⟩proj₂
    : {M : ▹ (Γ ⊢ A)}
    → Γ ⊢ proj₂ (next ⟨ M , next N ⟩) -→ N

  ξ-ƛ
    : Γ , A ⊢ M -→ M′
    → Γ     ⊢ ƛ next M -→ ƛ next M′

  ξ-·₁
    : {M : ▹ (Γ ⊢ A)}
    → Γ ⊢ L -→ L′
      ---------------
    → Γ ⊢ next L · M -→ next L′ · M

  ξ-·₂
    : {L : ▹ (Γ ⊢ A →̇ B)}
    → Γ ⊢ M -→ M′
      ---------------
    → Γ ⊢ L · next M -→ L · next M′

  ξ-⟨,⟩₁
    : {N : ▹ (Γ ⊢ B)}
    → Γ ⊢ M -→ M′
      ---------------
    → Γ ⊢ ⟨ next M , N ⟩ -→ ⟨ next M′ , N ⟩

  ξ-⟨,⟩₂
    : {M : ▹ (Γ ⊢ A)}
    → Γ ⊢ N -→ N′
      -------------------------------------
    → Γ ⊢ ⟨ M , next N ⟩ -→ ⟨ M , next N′ ⟩

  ξ-proj₁
    : Γ ⊢ L -→ L′
    → Γ ⊢ proj₁ next L -→ proj₁ next L′

  ξ-proj₂
    : Γ ⊢ L -→ L′
    → Γ ⊢ proj₂ next L -→ proj₂ next L′

------------------------------------------------------------------------------
-- Multi-step beta-reduction


data _⊢_-↠_ (Γ : Cxt) : Γ ⊢ A → Γ ⊢ A → Set where
  _∎ : (M : Γ ⊢ A) → Γ ⊢ M -↠ M

  _-→⟨_⟩_
    : ∀ L
    → Γ ⊢ L -→ M
    → Γ ⊢ M -↠ N
      ----------
    → Γ ⊢ L -↠ N

begin_
  : Γ ⊢ M -↠ N
  → Γ ⊢ M -↠ N
begin M-↠N = M-↠N

_-↠⟨_⟩_
  : ∀ L
  → Γ ⊢ L -↠ M
  → Γ ⊢ M -↠ N
  → Γ ⊢ L -↠ N
M -↠⟨ M ∎ ⟩ M-↠N                = M-↠N
L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

------------------------------------------------------------------------------
-- Multi-step reduction is a congruence

ƛ-↠
  : _ ⊢ M -↠ M′
  → _ ⊢ ƛ next M -↠ ƛ next M′
ƛ-↠ (M ∎)                 = ƛ next M ∎
ƛ-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
  ƛ next M -→⟨ ξ-ƛ M→M₁ ⟩ ƛ-↠ M₁-↠M₂

·₁-↠
  : {N : ▹ (Γ ⊢ _)}
  → _ ⊢ M -↠ M′
  → _ ⊢ (next M) · N -↠ (next M′) · N
·₁-↠ (M ∎)                 = next M · _ ∎
·₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
  next M · _ -→⟨ ξ-·₁ M→M₁ ⟩ ·₁-↠ M₁-↠M₂

·₂-↠
  : ∀ {M : ▹ (Γ ⊢ A →̇ B)}
  → _ ⊢ N -↠ N′
  → _ ⊢ M · (next N) -↠ M · (next N′)
·₂-↠ (N ∎)                 = _ · next N ∎
·₂-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
  _ · next N -→⟨ ξ-·₂ N→N₁ ⟩ ·₂-↠ N₁-↠N₂

·-↠
  : _ ⊢ M -↠ M′
  → _ ⊢ N -↠ N′
  → _ ⊢ next M · next N -↠ next M′ · next N′
·-↠ M-↠M′ N-↠N′ = begin
  _ · _
    -↠⟨ ·₁-↠ M-↠M′ ⟩
  _ · _
    -↠⟨ ·₂-↠ N-↠N′ ⟩
  _ · _ ∎ 

proj₁-↠
  : _ ⊢ L -↠ L′ → _ ⊢ proj₁ next L -↠ proj₁ next L′
proj₁-↠ (L ∎)                 = proj₁ next L ∎
proj₁-↠ (L -→⟨ L→L₁ ⟩ L₁-↠L₂) =
  proj₁ next L -→⟨ ξ-proj₁ L→L₁ ⟩ proj₁-↠ L₁-↠L₂

proj₂-↠
  : _ ⊢ L -↠ L′
  → _ ⊢ proj₂ next L -↠ proj₂ next L′
proj₂-↠ (L ∎)                 = proj₂ next L ∎
proj₂-↠ (L -→⟨ L→L₂ ⟩ L₂-↠L₂) =
  proj₂ next L -→⟨ ξ-proj₂ L→L₂ ⟩ proj₂-↠ L₂-↠L₂

⟨,⟩₁-↠
  : {N : ▹ (Γ ⊢ B)}
  → _ ⊢ M -↠ M′
  → _ ⊢ ⟨ next M , N ⟩ -↠ ⟨ next M′ , N ⟩
⟨,⟩₁-↠ (M ∎)                 = ⟨ next M , _ ⟩ ∎
⟨,⟩₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
  ⟨ next M , _ ⟩ -→⟨ ξ-⟨,⟩₁ M→M₁ ⟩ ⟨,⟩₁-↠ M₁-↠M₂


⟨,⟩₂-↠
  : {M : ▹ (Γ ⊢ A)}
  → _ ⊢ N -↠ N′
  → _ ⊢ ⟨ M , next N ⟩ -↠ ⟨ M , next N′ ⟩
⟨,⟩₂-↠ (N ∎)                 = ⟨ _ , next N ⟩ ∎
⟨,⟩₂-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
  ⟨ _ , next N ⟩ -→⟨ ξ-⟨,⟩₂ N→N₁ ⟩ ⟨,⟩₂-↠ N₁-↠N₂

⟨,⟩-↠
  : _ ⊢ M -↠ M′
  → _ ⊢ N -↠ N′
  → _ ⊢ ⟨ next M , next N ⟩ -↠ ⟨ next M′ , next N′ ⟩
⟨,⟩-↠ M↠M′ N↠N′ = begin
  ⟨ _ , _ ⟩
    -↠⟨ ⟨,⟩₁-↠ M↠M′ ⟩
  ⟨ _ , _ ⟩
    -↠⟨ ⟨,⟩₂-↠ N↠N′ ⟩
  ⟨ _ , _ ⟩
    ∎

------------------------------------------------------------------------------
-- Infinitary beta-reduction

data _⊢_-↠ᵍ_ (Γ : Cxt) : Γ ⊢ A → Γ ⊢ A → Set where
  -↠to-↠
    : Γ ⊢ M -↠  N
    → Γ ⊢ M -↠ᵍ N

  _-↠⟨_⟩_⟨_⟩·_⟨_⟩
    : {M M′ : ▹ (Γ ⊢ A →̇ B)} {N N′ : ▹ (Γ ⊢ A)}
    → (L : Γ ⊢ B)
    → Γ ⊢ L -↠ M · N
    → ▸ (λ α → Γ ⊢ M α -↠ᵍ M′ α)
    → ▸ (λ α → Γ ⊢ N α -↠ᵍ N′ α)
    → Γ ⊢ L -↠ᵍ M′ · N′

{-
data isRootStable : (M : Γ ⊢ A) → Set where
  `_ : {x : Γ ∋ A}
    → isRootStable (` x)

  ƛ_ : {M : ▹ (Γ , A ⊢ B)}
    → isRootStable (ƛ M)

  _·_ : {M : ▹ (Γ ⊢ A →̇ B)} {N : ▹ (Γ ⊢ A)}
    → isRootStable (M · N)
-}

open import Cubical.Foundations.Everything
  renaming (Type to 𝓤)
open import Cubical.Data.Sigma                   as C
  renaming (Type to 𝓤)
  hiding   (_×_)
open import Cubical.HITs.PropositionalTruncation

Prog : Type → 𝓤
Prog τ = ∅ ⊢ τ

isSurjective : {X : 𝓤} → (Prog A → X → 𝓤) → 𝓤
isSurjective _⊩_ = ∀ x → ∃[ a ∈ Prog _ ] a ⊩ x

record Asm : 𝓤₁ where
  field
    carrier    : 𝓤
    {type}     : Type
    _⊩_        : Prog type → carrier → 𝓤
    realiserOf : isSurjective _⊩_

  RealisabilityIsProp : isProp (isSurjective _⊩_)
  RealisabilityIsProp = isPropΠ (λ _ → propTruncIsProp)
open Asm using (type; carrier)

track : (X Y : Asm) → Prog (X .type →̇ Y .type)
  → (X .carrier → Y .carrier) → 𝓤
track X Y L h =
  ∀ M x → M ⊩x x → Σ[ N ∈ _ ] (∅ ⊢ (next L) · (next M) -↠ N) C.× N ⊩y h x
  where
    open Asm X renaming (_⊩_ to _⊩x_)
    open Asm Y renaming (_⊩_ to _⊩y_)

IsTrackable : (A B : Asm) → (A .carrier → B .carrier) → 𝓤
IsTrackable X Y h = Σ[ L ∈ _ ] track X Y L h

Trackable : (A B : Asm) → 𝓤
Trackable X Y = Σ[ f ∈ _ ] IsTrackable X Y f

infixr 6 _⇒_
_⇒_ : Asm → Asm → Asm
X ⇒ Y = record
  { _⊩_        = _⊩_
  ; realiserOf = h }
  where
    open Asm X renaming (carrier to |X|; _⊩_ to _⊩x_; realiserOf to f)
    open Asm Y renaming (carrier to |Y|; _⊩_ to _⊩y_; realiserOf to g)

    _⊩_ : Prog _ → Trackable X Y → 𝓤 
    L ⊩ (f , _)    = track X Y L f

    h : isSurjective _⊩_
    h (f , (L , L⊩f)) = ∣ L , L⊩f ∣

□ₐ_ : Asm → Asm
□ₐ X = record
  { _⊩_        = _⊩□_
  ; realiserOf = g }
  where
    open Asm X renaming (carrier to |X|; type to τ; realiserOf to f)

    _⊩□_
      : ∅ ⊢ τ
      → Σ[ M ∈ Prog τ ] Σ[ x ∈ ▹ |X| ] (▸ λ α → M ⊩ x α)
      → 𝓤
    M ⊩□ (N , _) = M ≡ N

    g : isSurjective _⊩□_
    g (M , (x , ▸M⊩x)) = ∣ M , refl ∣

Löb : (X : Asm) → Trackable (□ₐ (□ₐ X ⇒ X)) (□ₐ X)
Löb X = {!!} , {!!}
  where
    open Asm X renaming (carrier to |X|; type to τ; realiserOf to f)
    |□X| : 𝓤
    |□X| = Σ[ M ∈ Prog τ ] Σ[ x ∈ ▹ |X| ] (▸ λ α → M ⊩ x α)
 
    lob : (Σ[ L ∈ Prog {!!} ] Σ[ f ∈ ▹ Trackable (□ₐ X) X ] track {!!} {!!} {!!} {!fst f!}) → |□X|
    lob = {!!}
    
