{-# OPTIONS --without-K --safe #-}

module metric2.rationals where

open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Rational.Unnormalised as ℚ using () renaming (ℚᵘ to ℚ; 0ℚᵘ to 0ℚ; 1ℚᵘ to 1ℚ)
import Data.Rational.Unnormalised.Properties as ℚ
open import metric2.base
open import upper-reals

open MSpc
open _⇒_
open _≈f_

module _ where
  import Data.Integer as ℤ
  import Data.Nat as ℕ
  open import Relation.Binary.PropositionalEquality

  0≤∣p∣ : ∀ p → 0ℚ ℚ.≤ ℚ.∣ p ∣
  0≤∣p∣ (ℚ.mkℚᵘ (ℤ.+ ℕ.zero) _)    = ℚ.*≤* (ℤ.+≤+ ℕ.z≤n)
  0≤∣p∣ (ℚ.mkℚᵘ (ℤ.+ (ℕ.suc n)) _) = ℚ.*≤* (ℤ.+≤+ ℕ.z≤n)
  0≤∣p∣ (ℚ.mkℚᵘ (ℤ.-[1+ n ]) _)     = ℚ.*≤* (ℤ.+≤+ ℕ.z≤n)

  ∣∣p∣∣≡∣p∣ : ∀ p → ℚ.∣ ℚ.∣ p ∣ ∣ ≡ ℚ.∣ p ∣
  ∣∣p∣∣≡∣p∣ p = ℚ.0≤p⇒∣p∣≡p (0≤∣p∣ p)

  ∣∣p∣∣≃∣p∣ : ∀ p → ℚ.∣ ℚ.∣ p ∣ ∣ ℚ.≃ ℚ.∣ p ∣
  ∣∣p∣∣≃∣p∣ p = ℚ.≃-reflexive (∣∣p∣∣≡∣p∣ p)

ℚspc : MSpc
ℚspc .Carrier = ℚ
ℚspc .dist x y = rational ℚ.∣ x ℚ.- y ∣
ℚspc .refl {x} =
  begin
    rational ℚ.∣ x ℚ.- x ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-inverseʳ x)) ⟩
    rational ℚ.∣ 0ℚ ∣
  ≈⟨ rational-cong (ℚ.0≤p⇒∣p∣≃p ℚ.≤-refl) ⟩
    rational 0ℚ
  ≈⟨ rational-0 ⟩
    0ℝ
  ∎
  where open ≤-Reasoning
ℚspc .sym {x}{y} =
  begin
    rational ℚ.∣ x ℚ.- y ∣
  ≈⟨ rational-cong (ℚ.≃-sym (ℚ.∣-p∣≃∣p∣ (x ℚ.- y))) ⟩
    rational ℚ.∣ ℚ.- (x ℚ.- y) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (⁻¹-anti-homo-∙ x (ℚ.- y))) ⟩
    rational ℚ.∣ ℚ.- (ℚ.- y) ℚ.- x ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congˡ (ℚ.- x) (⁻¹-involutive y))) ⟩
    rational ℚ.∣ y ℚ.- x ∣
  ∎
  where open ≤-Reasoning
        open import Algebra.Properties.AbelianGroup ℚ.+-0-abelianGroup
ℚspc .triangle {x}{y}{z} =
  begin
    rational ℚ.∣ x ℚ.- z ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.+-identityʳ (x ℚ.- z)))) ⟩
    rational (ℚ.∣ (x ℚ.- z) ℚ.+ 0ℚ ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.+-congʳ (x ℚ.- z) (ℚ.+-inverseˡ y)))) ⟩
    rational (ℚ.∣ (x ℚ.- z) ℚ.+ (ℚ.- y ℚ.+ y) ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ-interchange x (ℚ.- z) (ℚ.- y) y)) ⟩
    rational (ℚ.∣ (x ℚ.- y) ℚ.+ ((ℚ.- z) ℚ.+ y) ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congʳ (x ℚ.- y) (ℚ.+-comm (ℚ.- z) y))) ⟩
    rational (ℚ.∣ (x ℚ.- y) ℚ.+ (y ℚ.- z) ∣)
  ≤⟨ rational-mono (ℚ.∣p+q∣≤∣p∣+∣q∣ (x ℚ.- y) (y ℚ.- z)) ⟩
    rational (ℚ.∣ x ℚ.- y ∣ ℚ.+ ℚ.∣ y ℚ.- z ∣)
  ≈⟨ ≃-sym (rational-+ ℚ.∣ x ℚ.- y ∣ ℚ.∣ y ℚ.- z ∣ (0≤∣p∣ (x ℚ.- y)) (0≤∣p∣ (y ℚ.- z))) ⟩
    rational ℚ.∣ x ℚ.- y ∣ + rational ℚ.∣ y ℚ.- z ∣
  ∎
  where open ≤-Reasoning

ℚspc-≈ : ∀ {q r} → q ℚ.≃ r → _≈_ ℚspc q r
ℚspc-≈ {q}{r} q≃r =
  begin
    rational ℚ.∣ q ℚ.- r ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congˡ (ℚ.- r) q≃r)) ⟩
    rational ℚ.∣ r ℚ.- r ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-inverseʳ r)) ⟩
    rational ℚ.∣ 0ℚ ∣
  ≈⟨ rational-cong (ℚ.0≤p⇒∣p∣≃p ℚ.≤-refl) ⟩
    rational 0ℚ
  ≈⟨ rational-0 ⟩
    0ℝ
  ∎
  where open ≤-Reasoning

open import metric2.monoidal
open import metric2.terminal
open import qpos as ℚ⁺ using (ℚ⁺)
open metric2.base.category

const : ℚ → ⊤ₘ ⇒ ℚspc
const q .fun _ = q
const q .non-expansive = ℚspc .refl {q}

------------------------------------------------------------------------------
-- ℚspc is a commutative monoid object in the category of metric
-- spaces and non-expansive maps

zero : ⊤ₘ ⇒ ℚspc
zero = const 0ℚ

add : (ℚspc ⊗ ℚspc) ⇒ ℚspc
add .fun (a , b) = a ℚ.+ b
add .non-expansive {a₁ , b₁}{a₂ , b₂} =
  begin
    rational ℚ.∣ a₁ ℚ.+ b₁ ℚ.- (a₂ ℚ.+ b₂) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congʳ (a₁ ℚ.+ b₁) (ℚ.≃-sym (⁻¹-∙-comm a₂ b₂)))) ⟩
    rational ℚ.∣ a₁ ℚ.+ b₁ ℚ.+ (ℚ.- a₂ ℚ.- b₂) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ-interchange a₁ b₁ (ℚ.- a₂) (ℚ.- b₂))) ⟩
    rational ℚ.∣ (a₁ ℚ.- a₂) ℚ.+ (b₁ ℚ.- b₂) ∣
  ≤⟨ rational-mono (ℚ.∣p+q∣≤∣p∣+∣q∣ (a₁ ℚ.- a₂) (b₁ ℚ.- b₂)) ⟩
    rational (ℚ.∣ a₁ ℚ.- a₂ ∣ ℚ.+ ℚ.∣ b₁ ℚ.- b₂ ∣)
  ≈⟨ ≃-sym (rational-+ ℚ.∣ a₁ ℚ.- a₂ ∣ ℚ.∣ b₁ ℚ.- b₂ ∣ (0≤∣p∣ (a₁ ℚ.- a₂)) (0≤∣p∣ (b₁ ℚ.- b₂))) ⟩
    rational ℚ.∣ a₁ ℚ.- a₂ ∣ + rational ℚ.∣ b₁ ℚ.- b₂ ∣
  ≈⟨ ≃-refl ⟩
    dist (ℚspc ⊗ ℚspc) (a₁ , b₁) (a₂ , b₂)
  ∎
  where open ≤-Reasoning
        open import Algebra.Properties.AbelianGroup (ℚ.+-0-abelianGroup)

add-identityˡ : (add ∘ (zero ⊗f id) ∘ left-unit⁻¹) ≈f id
add-identityˡ .f≈f a = ℚspc-≈ (ℚ.+-identityˡ a)

add-comm : (add ∘ swap) ≈f add
add-comm .f≈f (a , b) = ℚspc-≈ (ℚ.+-comm b a)

add-assoc : (add ∘ (add ⊗f id) ∘ ⊗-assoc) ≈f (add ∘ (id ⊗f add))
add-assoc .f≈f (a , (b , c)) = ℚspc-≈ (ℚ.+-assoc a b c)

------------------------------------------------------------------------------
-- Negation, so we have a (graded) abelian group object
open import metric2.scaling

negate : ℚspc ⇒ ℚspc
negate .fun a = ℚ.- a
negate .non-expansive {a}{b} =
  begin
    rational ℚ.∣ ℚ.- a ℚ.- ℚ.- b ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (⁻¹-∙-comm a (ℚ.- b))) ⟩
    rational ℚ.∣ ℚ.- (a ℚ.- b) ∣
  ≈⟨ rational-cong (ℚ.∣-p∣≃∣p∣ (a ℚ.- b)) ⟩
    dist ℚspc a b
  ∎
  where open ≤-Reasoning
        open import Algebra.Properties.AbelianGroup (ℚ.+-0-abelianGroup)

-- ![ 2 ] ℚspc → ℚspc
add-inverse : (add ∘ (id ⊗f negate) ∘ (derelict ⊗f derelict) ∘ duplicate) ≈f (zero ∘ discard)
add-inverse .f≈f q = ℚspc-≈ (ℚ.+-inverseʳ q)


------------------------------------------------------------------------------
-- Multiplication by a "scalar"

-- FIXME: make this work for any q : ℚ; need scaling to work for non-negative rationals
ℚ-scale : (q : ℚ⁺) → ![ q ] ℚspc ⇒ ℚspc
ℚ-scale q .fun a = ℚ⁺.fog q ℚ.* a
ℚ-scale q .non-expansive {a}{b} =
  begin
    rational ℚ.∣ ℚ⁺.fog q ℚ.* a ℚ.- ℚ⁺.fog q ℚ.* b ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congʳ (ℚ⁺.fog q ℚ.* a) (ℚ.neg-distribʳ-* (ℚ⁺.fog q) b))) ⟩
    rational ℚ.∣ ℚ⁺.fog q ℚ.* a ℚ.+ ℚ⁺.fog q ℚ.* (ℚ.- b) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.*-distribˡ-+ (ℚ⁺.fog q) a (ℚ.- b)))) ⟩
    rational ℚ.∣ ℚ⁺.fog q ℚ.* (a ℚ.- b) ∣
  ≈⟨ rational-cong (ℚ.∣p*q∣≃∣p∣*∣q∣ (ℚ⁺.fog q) (a ℚ.- b)) ⟩
    rational (ℚ.∣ ℚ⁺.fog q ∣ ℚ.* ℚ.∣ a ℚ.- b ∣)
  ≈⟨ ≃-sym (rational-* ℚ.∣ ℚ⁺.fog q ∣ ℚ.∣ a ℚ.- b ∣ (0≤∣p∣ (ℚ⁺.fog q)) (0≤∣p∣ (a ℚ.- b))) ⟩
    rational ℚ.∣ ℚ⁺.fog q ∣ * rational ℚ.∣ a ℚ.- b ∣
  ≈⟨ *-cong (rational-cong (ℚ.0≤p⇒∣p∣≃p (ℚ⁺.fog-nonneg {q}))) ≃-refl ⟩
    rational+ q * rational ℚ.∣ a ℚ.- b ∣
  ≈⟨ ≃-refl ⟩
    ![ q ] ℚspc .dist a b
  ∎
  where open ≤-Reasoning

------------------------------------------------------------------------------
-- Multiplication



{-
-- FIXME: the following need sub-ranges of ℚspc to be defined

-- if -a ≤ x₁,x₂ ≤ a, then ∣ x₁y₁ - x₂y₂ ∣ ≤ ∣ x₁y₁ ∣ + ∣ x₂y₂ ∣
--       | x₁ - x₂ ∣ + a * ∣ y₁ - y₂ ∣
--

-- ∣ a ∣ * ∣ y₁ - y₁ ∣ = ∣ ay₁ - ay₂ ∣


mul : ∀ a → (ℚspc[ - a , a ] ⊗ ![ ∣ a ∣ ] ℚspc) ⇒ ℚspc
mul = ?



recip : ∀ a → a > 0 → ![ a ] ℚspc[ a ⟩ ⇒ ℚspc
recip = ?
-}
