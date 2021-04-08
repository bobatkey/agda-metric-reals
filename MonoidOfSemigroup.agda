{-# OPTIONS --without-K --safe #-}

open import Level using (_⊔_)
open import Algebra

module MonoidOfSemigroup {m₁ m₂} (M : CommutativeSemigroup m₁ m₂) where

open import Data.Product using (_,_)
open import Relation.Binary

open CommutativeSemigroup M

data MCarrier : Set m₁ where
  u  : MCarrier
  `_ : Carrier → MCarrier

_⊕_ : MCarrier → MCarrier → MCarrier
u     ⊕ y     = y
(` x) ⊕ u     = ` x
(` x) ⊕ (` y) = ` (x ∙ y)

data _≃_ : MCarrier → MCarrier → Set (m₁ ⊔ m₂) where
  u≃u : u ≃ u
  x≃y : ∀ {x y} → x ≈ y → (` x) ≃ (` y)

≃-refl : ∀ {x} → x ≃ x
≃-refl {u}   = u≃u
≃-refl {` x} = x≃y refl

≃-sym : ∀ {x y} → x ≃ y → y ≃ x
≃-sym u≃u = u≃u
≃-sym (x≃y e) = x≃y (sym e)

≃-trans : ∀ {x y z} → x ≃ y → y ≃ z → x ≃ z
≃-trans u≃u       u≃u       = u≃u
≃-trans (x≃y eq₁) (x≃y eq₂) = x≃y (trans eq₁ eq₂)

≃-isEquivalence : IsEquivalence _≃_
≃-isEquivalence = record { refl = ≃-refl ; sym = ≃-sym ; trans = ≃-trans }

≃-setoid : Setoid m₁ (m₁ ⊔ m₂)
≃-setoid = record { isEquivalence = ≃-isEquivalence }

embedding : ∀ {x y} → (` x) ≃ (` y) → x ≈ y
embedding (x≃y e) = e

⊕-cong : Congruent₂ _≃_ _⊕_
⊕-cong u≃u         y₁≃y₂       = y₁≃y₂
⊕-cong (x≃y x₁≃x₂) u≃u         = x≃y x₁≃x₂
⊕-cong (x≃y x₁≃x₂) (x≃y y₁≃y₂) = x≃y (∙-cong x₁≃x₂ y₁≃y₂)

⊕-assoc : Associative _≃_ _⊕_
⊕-assoc u _ _ = ≃-refl
⊕-assoc (` _) u _ = ≃-refl
⊕-assoc (` _) (` _) u = ≃-refl
⊕-assoc (` x) (` y) (` z) = x≃y (assoc x y z)

⊕-comm : Commutative _≃_ _⊕_
⊕-comm u u = u≃u
⊕-comm u (` x) = ≃-refl
⊕-comm (` x) u = ≃-refl
⊕-comm (` x) (` y) = x≃y (comm x y)

+-identityʳ : RightIdentity _≃_ u _⊕_
+-identityʳ u     = ≃-refl
+-identityʳ (` x) = ≃-refl

+-identityˡ : LeftIdentity _≃_ u _⊕_
+-identityˡ u     = ≃-refl
+-identityˡ (` x) = ≃-refl

+-identity : Identity _≃_ u _⊕_
+-identity = +-identityˡ , +-identityʳ

------------------------------------------------------------------------
-- Algebraic Structures

⊕-isMagma : IsMagma _≃_ _⊕_
⊕-isMagma = record
  { isEquivalence = ≃-isEquivalence
  ; ∙-cong        = ⊕-cong
  }

⊕-isSemigroup : IsSemigroup _≃_ _⊕_
⊕-isSemigroup = record
  { isMagma = ⊕-isMagma
  ; assoc   = ⊕-assoc
  }

⊕-u-isMonoid : IsMonoid _≃_ _⊕_ u
⊕-u-isMonoid = record
  { isSemigroup = ⊕-isSemigroup
  ; identity    = +-identity
  }

⊕-u-isCommutativeMonoid : IsCommutativeMonoid _≃_ _⊕_ u
⊕-u-isCommutativeMonoid = record
  { isMonoid = ⊕-u-isMonoid
  ; comm     = ⊕-comm
  }

------------------------------------------------------------------------
-- Algebraic bundles

⊕-magma : Magma m₁ (m₁ ⊔ m₂)
⊕-magma = record
  { isMagma = ⊕-isMagma
  }

⊕-semigroup : Semigroup m₁ (m₁ ⊔ m₂)
⊕-semigroup = record
  { isSemigroup = ⊕-isSemigroup
  }

⊕-u-monoid : Monoid m₁ (m₁ ⊔ m₂)
⊕-u-monoid = record
  { isMonoid = ⊕-u-isMonoid
  }

⊕-u-commutativeMonoid : CommutativeMonoid m₁ (m₁ ⊔ m₂)
⊕-u-commutativeMonoid = record
  { isCommutativeMonoid = ⊕-u-isCommutativeMonoid
  }
