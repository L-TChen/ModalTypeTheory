{-# OPTIONS --without-K --allow-unsolved-metas #-}
module SystemT.GodelNumbering where

open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Function hiding (_∋_)
open import SystemT.Base hiding (□_; _,_)

private
  variable
    Γ : Cxt
    A B C : Type
    a b c : ∅ ⊢ A
    m n : ∅ ⊢ ℕ̇

record GodelNumbering : Set where
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
    -- the β-redex is for (∅ ⊢ igfix A · ⌜ a ⌝ -↠ ⌜ gfix a ⌝) to be true
    g : ∅ ⊢ ℕ̇ →̇ A
    g = (ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0))) · a

  gfix-spec : ∅ ⊢ gfix a -↠ a · ⌜ gfix a ⌝
  gfix-spec {A = A} {a = a} =
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
    where
      open -↠-Reasoning
      g : ∅ ⊢ ℕ̇ →̇ A
      g = (ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0))) · a

  -- ⊢ □ (□ A →̇ A) →̇ □ A
  igfix : (A : Type) → ∅ ⊢ ℕ̇ →̇ ℕ̇
  igfix A = ƛ ↑ diag · (↑ app · ↑ ⌜ ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0)) ⌝ · # 0)

  igfix-⌜⌝ : {a : ∅ ⊢ ℕ̇ →̇ A} → ∅ ⊢ igfix A · ⌜ a ⌝ -↠ ⌜ gfix a ⌝
  igfix-⌜⌝ {A = A} {a = a} =
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
    where
      open -↠-Reasoning
      g : ∅ ⊢ ℕ̇ →̇ A
      g = (ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0))) · a
      cong₃ : ∀ f {x y u v s t} → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
      cong₃ f P.refl P.refl P.refl = P.refl

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
