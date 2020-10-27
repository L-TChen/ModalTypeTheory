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
    n : ∅ ⊢ ℕ̇

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

  diag-gnum : ∅ ⊢ diag · ⌜ a ⌝ -↠ ⌜ a · ⌜ a ⌝ ⌝
  diag-gnum {a = a} =
    begin
      diag · ⌜ a ⌝
    -→⟨ β-ƛ· ⟩
      ↑ app ⟪ subst-zero ⌜ a ⌝ ⟫ · ⌜ a ⌝ · (↑ ignum ⟪ subst-zero ⌜ a ⌝ ⟫ · ⌜ a ⌝)
    ≡⟨ P.sym (P.cong (λ M → M · ⌜ a ⌝ · (↑ ignum ⟪ subst-zero ⌜ a ⌝ ⟫ · ⌜ a ⌝)) (subst-rename (λ ()) (subst-zero ⌜ a ⌝))) ⟩
      app ⟪ (λ ()) ⟫  · ⌜ a ⌝ · (↑ ignum ⟪ subst-zero ⌜ a ⌝ ⟫ · ⌜ a ⌝)
    -→⟨ {!!} ⟩
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
      {! ƛ ↑ M · (↑ diag · {!!}) !}
    -→⟨ {! !} ⟩
      a · ⌜ gfix a ⌝
    ∎
    where open -↠-Reasoning

  -- ⊢ □ (□ A →̇ A)   ⇒   ⊢ □ A
  igfix : (A : Type) → ∅ ⊢ ℕ̇ → ∅ ⊢ ℕ̇
  igfix A n = diag · g where
    -- n = gnum f
    -- g = gnum (ƛ x → f · (diag · x))
    --   = gnum ((ƛ y x → y · (diag · x)) · f)
    --   = app · (gnum (ƛ y x → y · (diag · x)) · gnum f
    --   = app · (gnum (ƛ y x → y · (diag · x)) · n
    -- g : □ (ℕ → A)
    g : ∅ ⊢ ℕ̇
    g = app · ⌜ ƛ ƛ_ {B = A} ((# 1) · (↑ diag · # 0)) ⌝ · n

  igfix-gnum : (a : ∅ ⊢ ℕ̇ →̇ A) → ∅ ⊢ ⌞ igfix A ⌜ a ⌝ ⌟ -↠ a · igfix A ⌜ a ⌝
  igfix-gnum = {!!}

  -- ⊢ □ (□ A →̇ A) →̇ □ A
  igfix′ : (A : Type) → ∅ ⊢ ℕ̇ →̇ ℕ̇
  igfix′ A = ƛ ↑ diag · (↑ app · ↑ ⌜ ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0)) ⌝ · # 0)
  igfix′-gnum : (a : ∅ ⊢ ℕ̇ →̇ A) → ∅ ⊢ ⌞ igfix′ A · ⌜ a ⌝ ⌟ -↠ a · (igfix′ A · ⌜ a ⌝)
  igfix′-gnum = {!!}

  -- ⊢ □ A →̇ A   ⇒   ⊢ A →̇ A   ⇒   ⊢ A
  selfEval⇒fixpoint
    : Σ[ e ∈ ∅ ⊢ ℕ̇ →̇ A ] (∀ n → ∅ ⊢ e · n -↠ ⌞ n ⌟)
    → (f : ∅ ⊢ A →̇ A)
    → Σ[ a ∈ ∅ ⊢ A ] (∅ ⊢ a -↠ f · a)
  selfEval⇒fixpoint (e , e-↠eval) f = (gfix (ƛ ↑ f · (↑ e · # 0))) , {! !}
  --   gfix (λ x → f · (e · x))
  -- -↠⟨ gfix-spec ⟩
  --   f · (e · ⌜ gfix (λ x → f · (e · x)) ⌝)
  -- -↠⟨ ·-cong₂ e-↠eval ⟩
  --   f · ⌞ ⌜ gfix (λ x → f · (e · x)) ⌝ ⌟
  -- -↠⟨ ·-cong₂ eval A ⟩
  --   f · gfix (λ x → suc (e · x))

  -- ¬ ∀ A. □ A → A
  ¬∃selfEval : (∀ A → Σ[ e ∈ ∅ ⊢ ℕ̇ →̇ A ] (∀ n → ∅ ⊢ e · n -↠ ⌞ n ⌟)) → ⊥
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
  ☒□X→̇X X n = ƛ ↑ ⌞ n ⌟ , proj₁ , λ { {a} {x , ⌞n⌟⊩x} tt → {! ⌞n⌟⊩x !} }

  ☒X→̇☒☒X : ∀ X a → Trackable (☒ X by a) (☒ (☒ X by a) by ⟨⟩)
  ☒X→̇☒☒X X _ = ƛ # 0 , (_, tt) , λ _ → tt
