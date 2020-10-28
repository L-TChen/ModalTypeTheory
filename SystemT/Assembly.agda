{-# OPTIONS --without-K #-}
module SystemT.Assembly where

open import Data.Product
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Function hiding (_∋_)
open import SystemT.Base hiding (□_; _,_)

private
  variable
    Γ : Cxt
    A B C : Type
    a b c : ∅ ⊢ A
    m n : ∅ ⊢ ℕ̇

record GNum : Set where
  field
    ⌜_⌝ : ∅ ⊢ A → ∅ ⊢ ℕ̇

    ⌞_⌟ : {A : Type} → ∅ ⊢ ℕ̇ → ∅ ⊢ A
    ⌞⌜⌝⌟-id : (∅ ⊢ n -↠ ⌜ a ⌝) → ⌞ n ⌟ ≡ a

    -- ⊢ □ (A → B) →̇ □ A →̇ □ B
    app : ∅ ⊢ ℕ̇ →̇ ℕ̇ →̇ ℕ̇
    app-⌜⌝-⌜⌝ : ∅ ⊢ app · ⌜ a ⌝ · ⌜ b ⌝ -↠ ⌜ a · b ⌝

    -- ⊢ □ A →̇ □ (□ A)
    ignum : ∅ ⊢ ℕ̇ →̇ ℕ̇
    ignum-⌜⌝ : ∅ ⊢ ignum · ⌜ a ⌝ -↠ ⌜ ⌜ a ⌝ ⌝

module _ {gNum : GNum} where
  open GNum gNum

  -- ⊢ □ (ℕ →̇ A) →̇ □ A
  diag : ∅ ⊢ ℕ̇ →̇ ℕ̇
  diag = ƛ ↑ app · # 0 · (↑ ignum · # 0)

  diag-⌜⌝ : ∅ ⊢ diag · ⌜ a ⌝ -↠ ⌜ a · ⌜ a ⌝ ⌝
  diag-⌜⌝ {a = a} =
    begin
      diag · ⌜ a ⌝
    -→⟨ β-ƛ· ⟩
      ↑ app ⟪ subst-zero ⌜ a ⌝ ⟫ · ⌜ a ⌝ · (↑ ignum ⟪ subst-zero ⌜ a ⌝ ⟫ · ⌜ a ⌝)
    ≡⟨ P.cong₂ (λ M N → M · ⌜ a ⌝ · (N · ⌜ a ⌝)) (subst-↑ _ app) (subst-↑ _ ignum) ⟩
      app · ⌜ a ⌝ · (ignum · ⌜ a ⌝)
    -↠⟨ ·₂-↠ ignum-⌜⌝ ⟩
      app · ⌜ a ⌝ · ⌜ ⌜ a ⌝ ⌝
    -↠⟨ app-⌜⌝-⌜⌝ ⟩
      ⌜ a · ⌜ a ⌝ ⌝
    ∎
    where open -↠-Reasoning

  -- ⊢ □ A →̇ A   ⇒   ⊢ A
  gfix : ∅ ⊢ ℕ̇ →̇ A → ∅ ⊢ A
  gfix {A} a = g · ⌜ g ⌝ where
    g : ∅ ⊢ ℕ̇ →̇ A
    g = ƛ ↑ a · (↑ diag · ` Z)

  gfix-spec : ∅ ⊢ gfix a -↠ a · ⌜ gfix a ⌝
  gfix-spec {a = a} =
    begin
      gfix a
    -→⟨ β-ƛ· ⟩
      ↑ a ⟪ subst-zero ⌜ g ⌝ ⟫ · (↑ diag ⟪ subst-zero ⌜ g ⌝ ⟫ · ⌜ g ⌝)
    ≡⟨ P.cong₂ (λ M N → M · (N · ⌜ g ⌝)) (subst-↑ _ a) (subst-↑ _ diag) ⟩
      a · (diag · ⌜ g ⌝)
    -↠⟨ ·₂-↠ diag-⌜⌝ ⟩
      a · ⌜ gfix a ⌝
    ∎
    where
      open -↠-Reasoning
      g : ∅ ⊢ ℕ̇ →̇ _
      g = ƛ ↑ a · (↑ diag · ` Z)

  -- ⊢ □ (□ A →̇ A) →̇ □ A
  igfix : (A : Type) → ∅ ⊢ ℕ̇ →̇ ℕ̇
  igfix A = ƛ ↑ diag · (↑ app · ↑ ⌜ ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0)) ⌝ · # 0)

  igfix-⌜⌝ : {a : ∅ ⊢ ℕ̇ →̇ A} → ∃[ b ] ((∅ ⊢ igfix A · ⌜ a ⌝ -↠ ⌜ b ⌝) × (∅ ⊢ b -↠ a · ⌜ b ⌝))
  igfix-⌜⌝ {A = A} {a = a} = g · ⌜ g ⌝ , igfix⌜a⌝-↠⌜g⌜g⌝⌝ , g⌜g⌝-↠a⌜g⌜g⌝⌝ where
    open -↠-Reasoning

    g : ∅ ⊢ ℕ̇ →̇ A
    g = (ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0))) · a

    cong₃ : ∀ f {x y u v s t} → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
    cong₃ f P.refl P.refl P.refl = P.refl

    igfix⌜a⌝-↠⌜g⌜g⌝⌝ : ∅ ⊢ igfix A · ⌜ a ⌝ -↠ ⌜ g · ⌜ g ⌝ ⌝
    igfix⌜a⌝-↠⌜g⌜g⌝⌝ =
      begin
        igfix A · ⌜ a ⌝
      -→⟨ β-ƛ· ⟩
        (↑ diag) ⟪ _ ⟫ · (↑ app ⟪ _ ⟫ · ↑ ⌜ ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0)) ⌝  ⟪ _ ⟫ · ⌜ a ⌝)
      ≡⟨ cong₃ (λ L M N → L · (M · N · ⌜ a ⌝)) (subst-↑ _ diag) (subst-↑ _ app) (subst-↑ _ _) ⟩
        diag · (app · ⌜ ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0)) ⌝ · ⌜ a ⌝)
      -↠⟨ ·₂-↠ app-⌜⌝-⌜⌝ ⟩
        diag · ⌜ g ⌝
      -↠⟨ diag-⌜⌝ ⟩
        ⌜ g · ⌜ g ⌝ ⌝
      ∎

    g⌜g⌝-↠a⌜g⌜g⌝⌝ :  ∅ ⊢ g · ⌜ g ⌝ -↠ a · ⌜ g · ⌜ g ⌝ ⌝
    g⌜g⌝-↠a⌜g⌜g⌝⌝ =
      begin
        g · ⌜ g ⌝
      -→⟨ ξ-·₁ β-ƛ· ⟩
        ƛ_ {B = A} (rename S_ a · (↑ diag ⟪ _ ⟫ · # 0)) · ⌜ g ⌝
      -→⟨ β-ƛ· ⟩
        rename S_ a ⟪ _ ⟫ · (↑ diag ⟪ _ ⟫ ⟪ _ ⟫ · ⌜ g ⌝)
      ≡⟨ P.cong₂ (λ M N → M · (N · ⌜ g ⌝)) (subst-rename-∅ S_ _ a) (subst-subst _ _ (↑ diag)) ⟩
        a · (↑ diag ⟪ _ ⟫ · ⌜ g ⌝)
      ≡⟨ P.cong (λ M → a · (M · ⌜ g ⌝)) (subst-↑ _ diag) ⟩
        a · (diag · ⌜ g ⌝)
      -↠⟨ ·₂-↠ diag-⌜⌝ ⟩
        a · ⌜ g · ⌜ g ⌝ ⌝
      ∎

  -- ⊢ □ A →̇ A   ⇒   ⊢ A →̇ A   ⇒   ⊢ A
  selfEval⇒fixpoint
    : Σ[ e ∈ ∅ ⊢ ℕ̇ →̇ A ] (∀ {n} → ∅ ⊢ e · n -↠ ⌞ n ⌟)
    → (f : ∅ ⊢ A →̇ A)
    → Σ[ a ∈ ∅ ⊢ A ] (∅ ⊢ a -↠ f · a)
  selfEval⇒fixpoint (e , e-↠⌞⌟) f = gfix (ƛ ↑ f · (↑ e · # 0)) ,
    (begin
      gfix (ƛ ↑ f · (↑ e · # 0))
    -↠⟨ gfix-spec ⟩
      (ƛ ↑ f · (↑ e · # 0)) · ⌜ gfix (ƛ ↑ f · (↑ e · # 0)) ⌝
    -→⟨ β-ƛ· ⟩
      ↑ f ⟪ _ ⟫ · (↑ e ⟪ _ ⟫ · ⌜ gfix (ƛ ↑ f · (↑ e · # 0)) ⌝)
    ≡⟨ P.cong₂ (λ M N → M · (N · ⌜ gfix (ƛ ↑ f · (↑ e · # 0)) ⌝)) (subst-↑ _ f) (subst-↑ _ e) ⟩
      f · (e · ⌜ gfix (ƛ ↑ f · (↑ e · # 0)) ⌝)
    -↠⟨ ·₂-↠ e-↠⌞⌟ ⟩
      f · (⌞ ⌜ gfix (ƛ ↑ f · (↑ e · # 0)) ⌝ ⌟)
    ≡⟨ P.cong (f ·_) (⌞⌜⌝⌟-id (_ ∎)) ⟩
      f · gfix (ƛ (↑ f) · ((↑ e) · # 0))
    ∎)
    where open -↠-Reasoning

  -- ¬ ∀ A. □ A → A
  ¬∃selfEval : (∀ A → Σ[ e ∈ ∅ ⊢ ℕ̇ →̇ A ] (∀ {n} → ∅ ⊢ e · n -↠ ⌞ n ⌟)) → ⊥
  ¬∃selfEval e with selfEval⇒fixpoint (e ℕ̇) (ƛ suc (# 0))
  ... | a , a-↠suca = {! !}

  rice
    : (d : ∅ ⊢ ℕ̇ →̇ ℕ̇) (a b : ∅ ⊢ A)
    → ((x y : ∅ ⊢ A) → ∅ ⊢ x -↠ y → ∅ ⊢ d · ⌜ x ⌝ -↠ d · ⌜ y ⌝)
    → ∅ ⊢ d · ⌜ a ⌝ -↠ zero
    → ∅ ⊢ d · ⌜ b ⌝ -↠ (suc zero)
    → ⊥
  rice d a b d-ext da-↠0 db-↠1 = {! d · gfix (ƛ n → ) !} where
    -- r = λ n. if d n then a else b
    -- gnum r = gnum (λ x y n. if d n then x else y) `app` ()
    --    d (gfix r)
    -- -↠ d (gnum (r · (gfix r))
    -- -↠ d (gnum (if d (gfix r) then a else b))
    -- -↠ { d ⌜ a ⌝ -↠ 0   if d (gfix r) -↠ 1
    --    ; d (gnum b) -↠ 1   if d (gfix r) -↠ 0

  record Assembly : Set₁ where
    field
      Carrier    : Set
      type       : Type
      _⊩_        : ∅ ⊢ type → Carrier → Set
      realiserOf : (x : Carrier) → ∃[ a ] (a ⊩ x)

  open Assembly

  Tracks : (X Y : Assembly) (r : ∅ ⊢ X .type →̇ Y .type) (f : X .Carrier → Y .Carrier) → Set
  Tracks X Y r f = {a : ∅ ⊢ X .type} {x : X .Carrier} → (X ._⊩_) a x → (Y ._⊩_) (r · a) (f x)

  Trackable : (X Y : Assembly) → Set
  Trackable X Y = ∃[ r ] ∃[ f ] (Tracks X Y r f)

  ⊥̇ : Assembly
  ⊥̇ = record { Carrier = ⊥
             ; type = ⊤̇
             ; _⊩_ = λ a x → ⊥
             ; realiserOf = λ () }

  _⇒_ : Assembly → Assembly → Assembly
  X ⇒ Y = record { Carrier = Trackable X Y ; type = (X .type) →̇ (Y .type) ; _⊩_ = λ r (_ , f , _) → Tracks X Y r f ; realiserOf = λ (r , f , r⊩f) → r , r⊩f }

  □_ : Assembly → Assembly
  □ X = record { Carrier = X .Carrier
               ; type = ℕ̇
               ; _⊩_ = λ a x → X ._⊩_ ⌞ a ⌟ x
               ; realiserOf = lift ∘ X .realiserOf } where
    lift : ∀ {x} → ∃[ a ] (X ._⊩_ a x) → ∃[ b ] (X ._⊩_ ⌞ b ⌟ x)
    lift (a , a⊩x) rewrite P.sym (⌞⌜⌝⌟-id (⌜ a ⌝ -↠-Reasoning.∎)) = ⌜ a ⌝ , a⊩x

  ☒_by_ : (X : Assembly) → (a : ∅ ⊢ X .type) → Assembly
  ☒ X by a = record { Carrier = ∃[ x ] (X ._⊩_ a x)  ; type = ⊤̇ ; _⊩_ = λ _ _ → ⊤ ; realiserOf = λ _ → ⟨⟩ , tt }

  ☒X→̇X : ∀ X a → Trackable (☒ X by a) X
  ☒X→̇X X a = ƛ (↑ a) , (λ (x , a⊩x) → x) , λ _ → {! a⊩x !}

  ☒X→̇□X : ∀ X a → Trackable (☒ X by a) (□ X)
  ☒X→̇□X X a = ƛ ↑ ⌜ a ⌝ , (λ (x , a⊩x) → x) , λ _ → {! eval-gnum a⊩x !}

  ¬☒X→̇□¬☒X : ∀ X a → Trackable ((☒ X by a) ⇒ ⊥̇) (□ ((☒ X by a) ⇒ ⊥̇))
  ¬☒X→̇□¬☒X X a = ƛ zero , id , λ r {_} {(x , a⊩x)} _ → r {⟨⟩} {x , a⊩x} tt

  ☒□X→̇X : ∀ X n → Trackable (☒ (□ X) by n) X
  ☒□X→̇X X n = ƛ ↑ ⌞ n ⌟ , (λ (x , x⊩a) → x) , λ { {a} {x , ⌞n⌟⊩x} tt → {! ⌞n⌟⊩x !} }

  ☒X→̇☒☒X : ∀ X a → Trackable (☒ X by a) (☒ (☒ X by a) by ⟨⟩)
  ☒X→̇☒☒X X _ = ƛ # 0 , (_, tt) , λ _ → tt

  ☒-intro : ∀ X → X .Carrier → ∃[ a ] ((☒ X by a) .Carrier)
  ☒-intro X x with a , a⊩x ←  X .realiserOf x = a , x , a⊩x

  ☒-internalize
    : ∀ X Y
    → (f : ∅ ⊢ X .type → ∅ ⊢ Y .type)
    → (∀ a → ∃[ x ] (X ._⊩_ a x) → ∃[ y ] (Y ._⊩_ (f a) y))
    → (∀ a → Trackable (☒ X by a) (☒ Y by f a))
  ☒-internalize X Y f g a = (ƛ # 0) , g a , λ x → tt

  -- non-provable in GLA
  IER : ∀ X a → Trackable (□ (☒ X by a)) X
  IER X a = ƛ (↑ a) , (λ (x , x⊩a) → x) , λ {_} {(x , a⊩x)} _ → {! !} 
