{-# OPTIONS --without-K --safe #-}

module qpos where

open import Algebra
open import Level using (0ℓ)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Rational.Unnormalised as ℚ using (↥_) renaming (ℚᵘ to ℚ; 0ℚᵘ to 0ℚ; 1ℚᵘ to 1ℚ)
import Data.Rational.Unnormalised.Properties as ℚ
open import Data.Integer as ℤ using (ℤ; +_)
import Data.Integer.Properties as ℤ
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality -- using (refl)
open import Relation.Nullary using (yes; no)

record ℚ⁺ : Set where
  constructor ⟨_,_⟩
  field
    rational : ℚ
    positive : ℚ.Positive rational
open ℚ⁺

infix  4 _≃_ -- _≠_
infix 4 _≤_ -- _<_ _≥_ _>_ _≰_ _≱_ _≮_ _≯_
infix  8 1/_ _/2
infixl 7 _*_
infixl 6 _+_

fog : ℚ⁺ → ℚ
fog q = q .rational

gof : ∀ q → q ℚ.> 0ℚ → ℚ⁺
gof q q>0 .rational = q
gof q q>0 .positive = ℚ.positive q>0

_+_ : ℚ⁺ → ℚ⁺ → ℚ⁺
(q + r) .rational = q .rational ℚ.+ r .rational
(q + r) .positive = ℚ.positive (ℚ.+-mono-< (ℚ.positive⁻¹ (q .positive)) (ℚ.positive⁻¹ (r .positive)))

_*_ : ℚ⁺ → ℚ⁺ → ℚ⁺
(q * r) .rational = q .rational ℚ.* r .rational
(q * r) .positive =
    ℚ.positive (ℚ.≤-<-trans (ℚ.≤-reflexive (ℚ.≃-sym (ℚ.*-zeroʳ (q .rational))))
                           (ℚ.*-monoʳ-<-pos {q .rational} (q .positive) (ℚ.positive⁻¹ {r .rational} (r .positive))))

positive⇒nonzero : ∀ {p} → ℚ.Positive p → ℤ.∣ ↥ p ∣ ℚ.≢0
positive⇒nonzero {ℚ.mkℚᵘ (+_ (suc n)) denominator-1} +ve = tt

1/-positive : ∀ p → (+ve : ℚ.Positive p) → ℚ.Positive (ℚ.1/_ p {positive⇒nonzero {p} +ve})
1/-positive (ℚ.mkℚᵘ (+_ (suc n)) d) tt = tt

1/_ : ℚ⁺ → ℚ⁺
(1/ q) .rational = ℚ.1/_ (q .rational) {positive⇒nonzero {q .rational} (q .positive)}
(1/ q) .positive = 1/-positive (q .rational) (q .positive)

½ : ℚ⁺
½ .rational = ℚ.½
½ .positive = tt

1ℚ⁺ : ℚ⁺
1ℚ⁺ .rational = 1ℚ
1ℚ⁺ .positive = tt

_/2 : ℚ⁺ → ℚ⁺
q /2 = ½ * q

data _≃_ : ℚ⁺ → ℚ⁺ → Set where
  r≃r : ∀ {q r} → q .rational ℚ.≃ r .rational → q ≃ r

data _≤_ : ℚ⁺ → ℚ⁺ → Set where
  r≤r : ∀ {q r} → q .rational ℚ.≤ r .rational → q ≤ r

data _<_ : ℚ⁺ → ℚ⁺ → Set where
  r<r : ∀ {q r} → q .rational ℚ.< r .rational → q < r

------------------------------------------------------------------------
-- Properties of the equivalence

≃-refl : Reflexive _≃_
≃-refl = r≃r ℚ.≃-refl

≃-sym : Symmetric _≃_
≃-sym (r≃r q≃r) = r≃r (ℚ.≃-sym q≃r)

≃-trans : Transitive _≃_
≃-trans (r≃r q≃r) (r≃r r≃s) = r≃r (ℚ.≃-trans q≃r r≃s)

≃-isEquivalence : IsEquivalence _≃_
≃-isEquivalence .IsEquivalence.refl {x} = ≃-refl {x}
≃-isEquivalence .IsEquivalence.sym {x} {y} = ≃-sym {x} {y}
≃-isEquivalence .IsEquivalence.trans {x} {y} {z} = ≃-trans {x} {y} {z}

≃-setoid : Setoid 0ℓ 0ℓ
≃-setoid .Setoid.Carrier = ℚ⁺
≃-setoid .Setoid._≈_ = _≃_
≃-setoid .Setoid.isEquivalence = ≃-isEquivalence

------------------------------------------------------------------------
-- Properties of _≤_

≤-refl : ∀ {q} → q ≤ q
≤-refl = r≤r ℚ.≤-refl

≤-reflexive : ∀ {q r} → q ≃ r → q ≤ r
≤-reflexive (r≃r eq) = r≤r (ℚ.≤-reflexive eq)

≤-trans : ∀ {q r s} → q ≤ r → r ≤ s → q ≤ s
≤-trans (r≤r q≤r) (r≤r r≤s) = r≤r (ℚ.≤-trans q≤r r≤s)

≤-isPreorder : IsPreorder _≃_ _≤_
≤-isPreorder = record
  { isEquivalence = ≃-isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

<-trans : Transitive _<_
<-trans (r<r i<j) (r<r j<k) = r<r (ℚ.<-trans i<j j<k)

<-respʳ-≃ : _<_ Respectsʳ _≃_
<-respʳ-≃ (r≃r i≃j) (r<r j<k) = r<r (ℚ.<-respʳ-≃ i≃j j<k)

<-respˡ-≃ : _<_ Respectsˡ _≃_
<-respˡ-≃ (r≃r i≃j) (r<r j<k) = r<r (ℚ.<-respˡ-≃ i≃j j<k)

<-resp-≃ : _<_ Respects₂ _≃_
<-resp-≃ = <-respʳ-≃ , <-respˡ-≃

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (r<r i<j) = r≤r (ℚ.<⇒≤ i<j)

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans (r<r i<j) (r≤r j≤k) = r<r (ℚ.<-≤-trans i<j j≤k)

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans (r≤r i≤j) (r<r j<k) = r<r (ℚ.≤-<-trans i≤j j<k)

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    <-resp-≃
    <⇒≤
    <-≤-trans
    ≤-<-trans
    public

------------------------------------------------------------------------
-- Properties of _+_

+-cong : Congruent₂ _≃_ _+_
+-cong (r≃r q₁≃q₂) (r≃r r₁≃r₂) = r≃r (ℚ.+-cong q₁≃q₂ r₁≃r₂)

+-congʳ : ∀ p {q r} → q ≃ r → p + q ≃ p + r
+-congʳ p q≃r = +-cong (≃-refl {p}) q≃r

+-congˡ : ∀ p {q r} → q ≃ r → q + p ≃ r + p
+-congˡ p q≃r = +-cong q≃r (≃-refl {p})

+-comm : Commutative _≃_ _+_
+-comm q r = r≃r (ℚ.+-comm (q .rational) (r .rational))

+-assoc : Associative _≃_ _+_
+-assoc q r s = r≃r (ℚ.+-assoc (q .rational) (r .rational) (s .rational))

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ (r≤r x≤y) (r≤r u≤v) = r≤r (ℚ.+-mono-≤ x≤y u≤v)

+-increasing : ∀ {q r} → q ≤ q + r
+-increasing {q}{r} = r≤r (ℚ.p≤p+q {q .rational}{r .rational} (ℚ.positive⇒nonNegative {r .rational} (r .positive)))

private
  blah : ∀ {q r} → q ℚ.≠ r → q ℚ.≤ r → q ℚ.< r
  blah q≠r (ℚ.*≤* q≤r) = ℚ.*<* (ℤ.≤∧≢⇒< q≤r (λ x → q≠r (ℚ.*≡* x) ))

{-
postulate -- FIXME
  ≤-split : ∀ {ε₁ ε₂} → ε₁ ≤ ε₂ → (ε₁ ≃ ε₂) ⊎ (Σ[ δ ∈ ℚ⁺ ] (ε₁ + δ ≃ ε₂))
  -- ≤-split {⟨ ε₁ , _ ⟩}{⟨ ε₂ , _ ⟩} (r≤r ε₁≤ε₂) with ε₁ ℚᵘ.≃? ε₂
  -- ... | yes ε₁≃ε₂ = inj₁ (r≃r ε₁≃ε₂) -- ⟨ ε₂ .rational ℚᵘ.- ε₁ .rational , ℚᵘ.positive {!ℚ.p≤q⇒0≤q-p!} ⟩ , {!!}
  -- ... | no ε₁≠ε₂  = inj₂ (⟨ ε₂ ℚᵘ.- ε₁ , ℚᵘ.positive (blah {!!} (ℚ.p≤q⇒0≤q-p ε₁≤ε₂)) ⟩ , r≃r {!!})
-}
------------------------------------------------------------------------
-- Properties of _*_

*-cong : Congruent₂ _≃_ _*_
*-cong (r≃r q₁≃q₂) (r≃r r₁≃r₂) = r≃r (ℚ.*-cong q₁≃q₂ r₁≃r₂)

*-congʳ : ∀ p {q r} → q ≃ r → p * q ≃ p * r
*-congʳ p q≃r = *-cong (≃-refl {p}) q≃r

*-congˡ : ∀ p {q r} → q ≃ r → q * p ≃ r * p
*-congˡ p q≃r = *-cong q≃r (≃-refl {p})

*-mono-≤ : _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
*-mono-≤ {x}{y}{u}{v} (r≤r x≤y) (r≤r u≤v) =
  r≤r (ℚ.≤-trans (ℚ.*-monoʳ-≤-pos {x .rational} (x .positive) u≤v)
                 (ℚ.*-monoˡ-≤-pos (v .positive) x≤y))

*-mono-< : _*_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
*-mono-< {x}{y}{u}{v} (r<r x<y) (r<r u<v) =
  r<r (ℚ.<-trans (ℚ.*-monoʳ-<-pos {x .rational} (x .positive) u<v)
                 (ℚ.*-monoˡ-<-pos (v .positive) x<y))

*-comm : Commutative _≃_ _*_
*-comm q r = r≃r (ℚ.*-comm (q .rational) (r .rational))

*-assoc : Associative _≃_ _*_
*-assoc q r s = r≃r (ℚ.*-assoc (q .rational) (r .rational) (s .rational))

*-identityˡ : LeftIdentity _≃_ 1ℚ⁺ _*_
*-identityˡ q = r≃r (ℚ.*-identityˡ (q .rational))

*-identityʳ : RightIdentity _≃_ 1ℚ⁺ _*_
*-identityʳ q = r≃r (ℚ.*-identityʳ (q .rational))

*-identity : Identity _≃_ 1ℚ⁺ _*_
*-identity = *-identityˡ , *-identityʳ

*-distribʳ-+ : _DistributesOverʳ_ _≃_ _*_ _+_
*-distribʳ-+ x y z = r≃r (ℚ.*-distribʳ-+ (x .rational) (y .rational) (z .rational))

*-distribˡ-+ : _DistributesOverˡ_ _≃_ _*_ _+_
*-distribˡ-+ x y z = r≃r (ℚ.*-distribˡ-+ (x .rational) (y .rational) (z .rational))

------------------------------------------------------------------------
-- Properties of 1/

1/-cong : Congruent₁ _≃_ 1/_
1/-cong {⟨ ℚ.mkℚᵘ (+_ (suc n₁)) d₁ , tt ⟩} {⟨ ℚ.mkℚᵘ (+_ (suc n₂)) d₂ , tt ⟩} (r≃r (ℚ.*≡* q₁≃q₂)) =
  r≃r (ℚ.*≡* (begin
                 + suc d₁ ℤ.* + suc n₂ ≡⟨ ℤ.*-comm (+ suc d₁) (+ suc n₂) ⟩
                 + suc n₂ ℤ.* + suc d₁ ≡⟨ sym (q₁≃q₂) ⟩
                 + suc n₁ ℤ.* + suc d₂ ≡⟨ ℤ.*-comm (+ suc n₁) (+ suc d₂) ⟩
                 + suc d₂ ℤ.* + suc n₁
               ∎))
  where
  open ≡-Reasoning

*-inverseˡ : LeftInverse _≃_ 1ℚ⁺ 1/_ _*_
*-inverseˡ q = r≃r (ℚ.*-inverseˡ (q .rational) {positive⇒nonzero {q .rational} (q .positive)})

*-inverseʳ : RightInverse _≃_ 1ℚ⁺ 1/_ _*_
*-inverseʳ q = r≃r (ℚ.*-inverseʳ (q .rational) {positive⇒nonzero {q .rational} (q .positive)})

*-inverse : Inverse _≃_ 1ℚ⁺ 1/_ _*_
*-inverse = *-inverseˡ , *-inverseʳ

------------------------------------------------------------------------
-- _+_ makes ℚ⁺ a commutative semigroup

+-isMagma : IsMagma _≃_ _+_
+-isMagma = record { isEquivalence = ≃-isEquivalence ; ∙-cong = +-cong }

+-isSemigroup : IsSemigroup _≃_ _+_
+-isSemigroup = record { isMagma = +-isMagma ; assoc = +-assoc }

+-isCommutativeSemigroup : IsCommutativeSemigroup _≃_ _+_
+-isCommutativeSemigroup = record { isSemigroup = +-isSemigroup ; comm = +-comm }

------------------------------------------------------------------------
-- Bundles (FIXME do more)

+-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
+-commutativeSemigroup = record
                         { isCommutativeSemigroup = +-isCommutativeSemigroup }

------------------------------------------------------------------------
-- _*_ and 1/_ are an Abelian group

*-isMagma : IsMagma _≃_ _*_
*-isMagma = record { isEquivalence = ≃-isEquivalence ; ∙-cong = *-cong }

*-isSemigroup : IsSemigroup _≃_ _*_
*-isSemigroup = record { isMagma = *-isMagma ; assoc = *-assoc }

*-isCommutativeSemigroup : IsCommutativeSemigroup _≃_ _*_
*-isCommutativeSemigroup = record { isSemigroup = *-isSemigroup ; comm = *-comm }

*-1-isMonoid : IsMonoid _≃_ _*_ 1ℚ⁺
*-1-isMonoid = record { isSemigroup = *-isSemigroup ; identity = *-identity }

*-1-isCommutativeMonoid : IsCommutativeMonoid _≃_ _*_ 1ℚ⁺
*-1-isCommutativeMonoid = record { isMonoid = *-1-isMonoid ; comm = *-comm }

*-1-isGroup : IsGroup _≃_ _*_ 1ℚ⁺ 1/_
*-1-isGroup = record { isMonoid = *-1-isMonoid ; inverse = *-inverse ; ⁻¹-cong = 1/-cong }

*-1-isAbelianGroup : IsAbelianGroup _≃_ _*_ 1ℚ⁺ 1/_
*-1-isAbelianGroup = record { isGroup = *-1-isGroup ; comm = *-comm }

-- FIXME: bundles

------------------------------------------------------------------------
-- Special stuff about halving

half+half : ∀ {q} → q /2 + q /2 ≃ q
half+half {q} =
  begin
     q /2 + q /2       ≈⟨ ≃-refl ⟩
     (½ * q) + (½ * q) ≈⟨ ≃-sym (*-distribʳ-+ q ½ ½) ⟩
     (½ + ½) * q       ≈⟨ *-congˡ q {½ + ½} {1ℚ⁺} (r≃r (ℚ.*≡* refl)) ⟩
     1ℚ⁺ * q           ≈⟨ *-identityˡ q ⟩
     q
  ∎
  where open import Relation.Binary.Reasoning.Setoid (≃-setoid)

half-≤ : ∀ q → q /2 ≤ q
half-≤ q =
  begin
    q /2
      ≈⟨ ≃-refl ⟩
    ½ * q
      ≤⟨ *-mono-≤ {½} {1ℚ⁺} (r≤r (ℚ.*≤* (ℤ.+≤+ (ℕ.s≤s ℕ.z≤n)))) ≤-refl ⟩
    1ℚ⁺ * q
      ≈⟨ *-identityˡ q ⟩
    q
  ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- fog gof properties

fog-positive : ∀ {q} → 0ℚ ℚ.< fog q
fog-positive {q} = ℚ.positive⁻¹ (q .positive)

fog-nonneg : ∀ {q} → 0ℚ ℚ.≤ fog q
fog-nonneg {q} = ℚ.<⇒≤ (fog-positive {q})

fog-cong : ∀ {q r} → q ≃ r → fog q ℚ.≃ fog r
fog-cong (r≃r e) = e

fog-mono : ∀ {q r} → q ≤ r → fog q ℚ.≤ fog r
fog-mono (r≤r e) = e

+-fog : ∀ q r → fog (q + r) ℚ.≃ fog q ℚ.+ fog r
+-fog q r = ℚ.*≡* refl

*-fog : ∀ q r → fog (q * r) ℚ.≃ fog q ℚ.* fog r
*-fog q r = ℚ.*≡* refl

------------------------------------------------------------------------------
-- floor

open import Data.Nat.DivMod using (_/_; m/n*n≤m)

floor : ℚ⁺ → ℕ
floor ⟨ ℚ.mkℚᵘ (+ n) d-1 , _ ⟩ = n / suc d-1

fromℕ : ℕ → ℚ
fromℕ n = ℚ.mkℚᵘ (+ n) 0

floor-lower : ∀ q → fromℕ (floor q) ℚ.≤ fog q
floor-lower ⟨ ℚ.mkℚᵘ (+ n) d-1 , _ ⟩ =
  ℚ.*≤* (ℤ.≤-trans (ℤ.≤-reflexive (ℤ.+◃n≡+n _)) (ℤ.≤-trans (ℤ.+≤+ (ℕ.≤-trans (m/n*n≤m n (suc d-1)) (ℕ.≤-reflexive (sym (ℕ.*-identityʳ n))))) (ℤ.≤-reflexive (sym (ℤ.+◃n≡+n _)))))

-- floor-upper : ∀ q → fog q ℚ.< fromℕ (suc (floor q))
-- floor-upper ⟨ ℚ.mkℚᵘ (+ n) d-1 , _ ⟩ = ℚ.*<* {!!}

------------------------------------------------------------------------------
nn+pos : ∀ q (r : ℚ⁺) → 0ℚ ℚ.≤ q → ℚ⁺
nn+pos q r 0≤q .rational = q ℚ.+ fog r
nn+pos q r 0≤q .positive =
  ℚ.positive (ℚ.≤-<-trans (ℚ.≤-reflexive (ℚ.≃-sym (ℚ.+-identityʳ 0ℚ)))
             (ℚ.≤-<-trans (ℚ.+-monoˡ-≤ 0ℚ 0≤q)
                          (ℚ.+-monoʳ-< q (ℚ.positive⁻¹ (r .positive)))))
