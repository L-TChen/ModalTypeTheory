{-# OPTIONS --without-K #-}
module SystemT.PER where

open import Data.Product as Product using (_×_; ∃-syntax; Σ-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Relation.Binary using (Transitive; Symmetric)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Function using (id; _∘_; const)

open import SystemT.Base hiding (□_; _,_; _∋_)
open import SystemT.GodelNumbering

------------------------------------------------------------------------
-- Properties of _≤_

m≤n⇒m≤n+1 : ∀ {m n} → m ≤ n → m ≤ suc n
m≤n⇒m≤n+1 z≤n         = z≤n
m≤n⇒m≤n+1 (s≤s m+1≤n) = s≤s (m≤n⇒m≤n+1 m+1≤n)

m+1≤n+1⇒m≤n : ∀ {m n} → suc m ≤ suc n → m ≤ n
m+1≤n+1⇒m≤n (s≤s m≤n) = m≤n

m+1≤n⇒m≤n : ∀ {m n} → suc m ≤ n → m ≤ n
m+1≤n⇒m≤n = m+1≤n+1⇒m≤n ∘ m≤n⇒m≤n+1

module _ {godelNumbering : GodelNumbering} where
  open GodelNumbering godelNumbering

  infixr 7 _⇒_
  infix  9 □_

  record PER : Set₁ where
    field
      type        : Type
      _~[_]_      : ∅ ⊢ type → ℕ → ∅ ⊢ type → Set
      sym         : ∀ i → Symmetric _~[ i ]_
      trans       : ∀ i → Transitive _~[ i ]_
      restriction : ∀ i {a b} → a ~[ suc i ] b → a ~[ i ] b

  _∋[_]_ : (X : PER) → ℕ → (∅ ⊢ PER.type X) → Set
  X ∋[ i ] a  = PER._~[_]_ X a i a

  _∋_ : (X : PER) → (∅ ⊢ PER.type X) → Set
  X ∋ a  = ∀ i → X ∋[ i ] a

  _⇒_ : PER → PER → PER
  X ⇒ Y = record { type = A →̇ B; _~[_]_ = _~[_]_; trans = trans; sym = sym; restriction = restriction }
    where
      open PER X renaming (type to A; _~[_]_ to _~ˣ[_]_; sym to ~ˣ-sym; trans to ~ˣ-trans; restriction to rˣ)
      open PER Y renaming (type to B; _~[_]_ to _~ʸ[_]_; sym to ~ʸ-sym; trans to ~ʸ-trans; restriction to rʸ)

      -- TODO: Use c =β r · a, d =β r · a here
      _~[_]_ : ∅ ⊢ A →̇ B → ℕ → ∅ ⊢ A →̇ B → Set
      r ~[ i ] s = ∀ {a b c d j} → .(j ≤ i) → a ~ˣ[ j ] b → ∅ ⊢ c -↠ r · a → ∅ ⊢ d -↠ s · b → c ~ʸ[ j ] d

      sym : ∀ i → Symmetric _~[ i ]_
      sym i r~s {j = j} j≤i a~b c-↠ra d-↠sb = ~ʸ-sym j (r~s j≤i (~ˣ-sym j a~b) d-↠sb c-↠ra)

      trans : ∀ i → Transitive _~[ i ]_
      trans i r~s s~t {j = j} j≤i a~b c-↠ra d-↠tb = ~ʸ-trans j (r~s j≤i a~b c-↠ra -↠-refl) (s~t j≤i b~b -↠-refl d-↠tb)
        where b~b = ~ˣ-trans j (~ˣ-sym j a~b) a~b

      restriction : ∀ i {a b} → a ~[ suc i ] b → a ~[ i ] b
      restriction i r~s j≤i = r~s (m≤n⇒m≤n+1 j≤i)

  ⊥̇ : PER
  ⊥̇ = record
    { type = ⊤̇
    ; _~[_]_ = λ a i b → ⊥
    ; trans = λ i ()
    ; sym = λ i ()
    ; restriction = λ i ()
    }

  □_ : PER → PER
  □ X = record { type = ℕ̇; _~[_]_ = _~[_]_; trans = trans; sym = sym; restriction = restriction }
    where
      open PER X renaming (type to A; _~[_]_ to _~ˣ[_]_; sym to ~ˣ-sym; trans to ~ˣ-trans; restriction to rˣ)
      _~[_]_ : ∅ ⊢ ℕ̇ → ℕ → ∅ ⊢ ℕ̇ → Set
      m ~[ zero  ] n = Σ[ a ∈ ∅ ⊢ A ] ((∅ ⊢ m -↠ ⌜ a ⌝) × (∅ ⊢ n -↠ ⌜ a ⌝) × ⊤)
      m ~[ suc i ] n = Σ[ a ∈ ∅ ⊢ A ] ((∅ ⊢ m -↠ ⌜ a ⌝) × (∅ ⊢ n -↠ ⌜ a ⌝) × (X ∋[ i ] a))

      sym : ∀ i → Symmetric _~[ i ]_
      sym zero    (a , m-↠⌜a⌝ , n-↠⌜a⌝ , tt ) = a , n-↠⌜a⌝ , m-↠⌜a⌝ , tt
      sym (suc i) (a , m-↠⌜a⌝ , n-↠⌜a⌝ , X∋a) = a , n-↠⌜a⌝ , m-↠⌜a⌝ , X∋a

      -- TODO
      -- By (normality of ⌜a⌝, ⌜b⌝ , n-↠⌜a⌝ , n-↠⌜b⌝), ⌜a⌝ ≡ ⌜b⌝ (needs confluence), thus a ≡ b by injectivity of ⌜_⌝
      trans : ∀ i → Transitive _~[ i ]_
      trans zero    (a , m-↠⌜a⌝ , n-↠⌜a⌝ , tt)  (b , n-↠⌜b⌝ , o-↠⌜b⌝ , tt ) = {! !}
      trans (suc i) (a , m-↠⌜a⌝ , n-↠⌜a⌝ , X∋a) (b , n-↠⌜b⌝ , o-↠⌜b⌝ , X∋b) = {! !}

      restriction : ∀ i {a b} → a ~[ suc i ] b → a ~[ i ] b
      restriction zero    (a , m-↠⌜a⌝ , n-↠⌜a⌝ , _  ) = a , m-↠⌜a⌝ , n-↠⌜a⌝ , tt
      restriction (suc i) (a , m-↠⌜a⌝ , n-↠⌜a⌝ , X∋a) = a , m-↠⌜a⌝ , n-↠⌜a⌝ , rˣ i X∋a

  lob : ∀ {X} i r → (□ X ⇒ X) ∋[ i ] r → X ∋[ i ] gfix r
  lob zero    r □X⇒X∋r = □X⇒X∋r ≤-refl (gfix r , -↠-refl , -↠-refl , tt) gfix-spec gfix-spec
  lob {X = X} (suc i) r □X⇒X∋r = □X⇒X∋r ≤-refl (gfix r , -↠-refl , -↠-refl , lob i r (PER.restriction (□ X ⇒ X) i □X⇒X∋r)) gfix-spec gfix-spec

  GL : ∀ X → ∃[ r ] ((□ (□ X ⇒ X) ⇒ □ X) ∋ r)
  GL X = igfix (PER.type X) , gs
    where
      gs : ∀ i → (□ (□ X ⇒ X) ⇒ □ X) ∋[ i ] igfix (PER.type X)
      gs i {j = zero}  j≤i (r , m-↠⌜r⌝ , n-↠⌜r⌝ , ⊤     ) c-↠igfixm d-↠igfixn =
        gfix r , -↠-trans (-↠-trans c-↠igfixm (·₂-↠ m-↠⌜r⌝)) igfix-⌜⌝ , -↠-trans (-↠-trans d-↠igfixn (·₂-↠ n-↠⌜r⌝)) igfix-⌜⌝ , tt
      gs i {j = suc j} j≤i (r , m-↠⌜r⌝ , n-↠⌜r⌝ , □X⇒X∋r) c-↠igfixm d-↠igfixn =
        gfix r , -↠-trans (-↠-trans c-↠igfixm (·₂-↠ m-↠⌜r⌝)) igfix-⌜⌝ , -↠-trans (-↠-trans d-↠igfixn (·₂-↠ n-↠⌜r⌝)) igfix-⌜⌝ , lob j r □X⇒X∋r

