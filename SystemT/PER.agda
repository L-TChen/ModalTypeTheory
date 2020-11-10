{-# OPTIONS --without-K #-}
module SystemT.PER where

open import Data.Product as Product using (_×_; ∃-syntax; Σ-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Relation.Binary using (Transitive; Symmetric; _Respects_; _Respectsʳ_; _Respectsˡ_)
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
      type         : Type
      _~[_]_       : ∅ ⊢ type → ℕ → ∅ ⊢ type → Set
      respectsʳ-≡β : ∀ {i} → (_~[ i ]_) Respectsʳ (∅ ⊢_≡β_)
      sym          : ∀ i → Symmetric _~[ i ]_
      trans        : ∀ i → Transitive _~[ i ]_
      restriction  : ∀ i {a b} → a ~[ suc i ] b → a ~[ i ] b

    respectsˡ-≡β : ∀ {i} → (_~[ i ]_) Respectsˡ (∅ ⊢_≡β_)
    respectsˡ-≡β a≡βb a~c = sym _ (respectsʳ-≡β a≡βb (sym _ a~c))


  _∋[_]_ : (X : PER) → ℕ → (∅ ⊢ PER.type X) → Set
  X ∋[ i ] a  = PER._~[_]_ X a i a

  ∋-respects-≡β : ∀ {X i} → (X ∋[ i ]_) Respects (∅ ⊢_≡β_)
  ∋-respects-≡β {X} a≡b X∋a = PER.respectsˡ-≡β X a≡b (PER.respectsʳ-≡β X a≡b X∋a)

  _∋_ : (X : PER) → (∅ ⊢ PER.type X) → Set
  X ∋ a  = ∀ i → X ∋[ i ] a

  _⇒_ : PER → PER → PER
  X ⇒ Y = record
    { type = A →̇ B
    ; _~[_]_ = _~[_]_
    ; respectsʳ-≡β = respectsʳ-≡β
    ; trans = trans
    ; sym = sym
    ; restriction = restriction
    }
    where
      open PER X renaming (type to A; _~[_]_ to _~ˣ[_]_; respectsʳ-≡β to ~ˣ-respectsʳ-≡β; sym to ~ˣ-sym; trans to ~ˣ-trans; restriction to rˣ)
      open PER Y renaming (type to B; _~[_]_ to _~ʸ[_]_; respectsʳ-≡β to ~ʸ-respectsʳ-≡β; sym to ~ʸ-sym; trans to ~ʸ-trans; restriction to rʸ)

      _~[_]_ : ∅ ⊢ A →̇ B → ℕ → ∅ ⊢ A →̇ B → Set
      r ~[ i ] s = ∀ {a b j} → .(j ≤ i) → a ~ˣ[ j ] b → (r · a) ~ʸ[ j ] (s · b)

      respectsʳ-≡β : ∀ {i} → (_~[ i ]_) Respectsʳ (∅ ⊢_≡β_)
      respectsʳ-≡β r≡βs t~r j≤i a~b = ~ʸ-respectsʳ-≡β (·₁≡β r≡βs) (t~r j≤i a~b)

      sym : ∀ i → Symmetric _~[ i ]_
      sym i r~s {j = j} j≤i a~b = ~ʸ-sym j (r~s j≤i (~ˣ-sym j a~b))

      trans : ∀ i → Transitive _~[ i ]_
      trans i r~s s~t {j = j} j≤i a~b = ~ʸ-trans j (r~s j≤i a~b) (s~t j≤i b~b)
        where b~b = ~ˣ-trans j (~ˣ-sym j a~b) a~b

      restriction : ∀ i {a b} → a ~[ suc i ] b → a ~[ i ] b
      restriction i r~s j≤i = r~s (m≤n⇒m≤n+1 j≤i)

  ⊥̇ : PER
  ⊥̇ = record
    { type = ⊤̇
    ; _~[_]_ = λ a i b → ⊥
    ; respectsʳ-≡β = λ _ ()
    ; trans = λ i ()
    ; sym = λ i ()
    ; restriction = λ i ()
    }

  □_ : PER → PER
  □ X = record
    { type = ℕ̇
    ; _~[_]_ = _~[_]_
    ; respectsʳ-≡β = respectsʳ-≡β
    ; trans = trans
    ; sym = sym
    ; restriction = restriction
    }
    where
      open PER X renaming (type to A; _~[_]_ to _~ˣ[_]_; respectsʳ-≡β to ~ˣ-respectsʳ-≡β; sym to ~ˣ-sym; trans to ~ˣ-trans; restriction to rˣ)
      _~[_]_ : ∅ ⊢ ℕ̇ → ℕ → ∅ ⊢ ℕ̇ → Set
      m ~[ zero  ] n = Σ[ a ∈ ∅ ⊢ A ] ((∅ ⊢ m ≡β ⌜ a ⌝) × (∅ ⊢ n ≡β ⌜ a ⌝) × ⊤)
      m ~[ suc i ] n = Σ[ a ∈ ∅ ⊢ A ] ((∅ ⊢ m ≡β ⌜ a ⌝) × (∅ ⊢ n ≡β ⌜ a ⌝) × (X ∋[ i ] a))
 
      respectsʳ-≡β : ∀ {i} → (_~[ i ]_) Respectsʳ (∅ ⊢_≡β_)
      respectsʳ-≡β {zero}  m≡βn (a , o≡β⌜a⌝ , m≡β⌜a⌝ , tt ) = a , o≡β⌜a⌝ , ≡β-trans (≡β-sym m≡βn) m≡β⌜a⌝ , tt
      respectsʳ-≡β {suc i} m≡βn (a , o≡β⌜a⌝ , m≡β⌜a⌝ , X∋a) = a , o≡β⌜a⌝ , ≡β-trans (≡β-sym m≡βn) m≡β⌜a⌝ , X∋a

      sym : ∀ i → Symmetric _~[ i ]_
      sym zero    (a , m≡β⌜a⌝ , n≡β⌜a⌝ , tt ) = a , n≡β⌜a⌝ , m≡β⌜a⌝ , tt
      sym (suc i) (a , m≡β⌜a⌝ , n≡β⌜a⌝ , X∋a) = a , n≡β⌜a⌝ , m≡β⌜a⌝ , X∋a
 
      trans : ∀ i → Transitive _~[ i ]_
      trans zero    (a , m≡β⌜a⌝ , n≡β⌜a⌝ , tt)  (b , n≡β⌜b⌝ , o≡β⌜b⌝ , tt ) = a , m≡β⌜a⌝ , o≡β⌜a⌝ , tt
        where o≡β⌜a⌝ = (≡β-trans o≡β⌜b⌝ (≡β-trans (≡β-sym n≡β⌜b⌝) n≡β⌜a⌝))
      trans (suc i) (a , m≡β⌜a⌝ , n≡β⌜a⌝ , X∋a) (b , n≡β⌜b⌝ , o≡β⌜b⌝ , X∋b) = a , m≡β⌜a⌝ , o≡β⌜a⌝ , X∋a
        where o≡β⌜a⌝ = (≡β-trans o≡β⌜b⌝ (≡β-trans (≡β-sym n≡β⌜b⌝) n≡β⌜a⌝))
 
      restriction : ∀ i {a b} → a ~[ suc i ] b → a ~[ i ] b
      restriction zero    (a , m≡β⌜a⌝ , n≡β⌜a⌝ , _  ) = a , m≡β⌜a⌝ , n≡β⌜a⌝ , tt
      restriction (suc i) (a , m≡β⌜a⌝ , n≡β⌜a⌝ , X∋a) = a , m≡β⌜a⌝ , n≡β⌜a⌝ , rˣ i X∋a

  lob : ∀ {X} i r → (□ X ⇒ X) ∋[ i ] r → X ∋[ i ] gfix r
  lob {X = X} zero    r □X⇒X∋r = ∋-respects-≡β {X = X} (≡β-sym (-↠-to-≡β gfix-spec)) (□X⇒X∋r ≤-refl (gfix r , ≡β-refl , ≡β-refl , tt))
  lob {X = X} (suc i) r □X⇒X∋r = ∋-respects-≡β {X = X} (≡β-sym (-↠-to-≡β gfix-spec)) (□X⇒X∋r ≤-refl (gfix r , ≡β-refl , ≡β-refl , lob i r (PER.restriction (□ X ⇒ X) i □X⇒X∋r)))

  GL : ∀ X → ∃[ r ] ((□ (□ X ⇒ X) ⇒ □ X) ∋ r)
  GL X = igfix (PER.type X) , gs
    where
      gs : ∀ i → (□ (□ X ⇒ X) ⇒ □ X) ∋[ i ] igfix (PER.type X)
      gs i {j = zero}  j≤i (r , m≡β⌜r⌝ , n≡β⌜r⌝ , ⊤     ) =
        gfix r , ≡β-trans (·₂≡β m≡β⌜r⌝) (-↠-to-≡β igfix-⌜⌝) , ≡β-trans (·₂≡β n≡β⌜r⌝) (-↠-to-≡β igfix-⌜⌝) , tt
      gs i {j = suc j} j≤i (r , m≡β⌜r⌝ , n≡β⌜r⌝ , □X⇒X∋r) =
        gfix r , ≡β-trans (·₂≡β m≡β⌜r⌝) (-↠-to-≡β igfix-⌜⌝) , ≡β-trans (·₂≡β n≡β⌜r⌝) (-↠-to-≡β igfix-⌜⌝) , lob j r □X⇒X∋r
