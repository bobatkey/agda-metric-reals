{-# OPTIONS --without-K --safe #-}

module MetricSpace.Scaling where

open import Data.Product using (_,_)
open import MetricSpace
open import MetricSpace.MonoidalProduct
open import Data.Real.UpperClosed
import Data.Rational.Unnormalised.Positive as ℚ⁺
open ℚ⁺ using (ℚ⁺; 1ℚ⁺)
open MetricSpace.category

open MSpc
open _⇒_
open _≈f_

-- A graded comonad, for expressing sensitivity wrt inputs

-- FIXME: ought to be ℚ≥0, or even ℝᵘ (but that isn't a set! is that a
-- problem?)
![_] : ℚ⁺ → MSpc → MSpc
![ ε ] X .Carrier = X .Carrier
![ ε ] X .dist x y = rational+ ε * X .dist x y
![ ε ] X .refl {x} =
  begin
    rational+ ε * X .dist x x
  ≤⟨ *-mono-≤ ≤-refl (X .refl) ⟩
    rational+ ε * 0ℝ
  ≈⟨ *-zeroʳ (rational+ ε) (rational+<∞ ε) ⟩
    0ℝ
  ∎
  where open ≤-Reasoning
![ ε ] X .sym {x}{y} =
  begin
    rational+ ε * X .dist x y
  ≤⟨ *-mono-≤ ≤-refl (X .sym) ⟩
    rational+ ε * X .dist y x
  ∎
  where open ≤-Reasoning
![ ε ] X .triangle {x}{y}{z} =
  begin
    rational+ ε * X .dist x z
  ≤⟨ *-mono-≤ ≤-refl (X .triangle) ⟩
    rational+ ε * (X .dist x y + X .dist y z)
  ≈⟨ *-distribˡ-+ (rational+ ε) (X .dist x y) (X .dist y z) ⟩
    (rational+ ε * X .dist x y) + (rational+ ε * X .dist y z)
  ∎
  where open ≤-Reasoning

map : ∀ {ε X Y} → X ⇒ Y → ![ ε ] X ⇒ ![ ε ] Y
map f .fun x = f .fun x
map f .non-expansive = *-mono-≤ ≤-refl (f .non-expansive)

map-cong : ∀ {ε X Y} {f₁ f₂ : X ⇒ Y} → f₁ ≈f f₂ → map {ε} f₁ ≈f map {ε} f₂
map-cong {ε}{X}{Y} {f₁}{f₂} f₁≈f₂ .f≈f x =
  begin
    rational+ ε * Y .dist (f₁ .fun x) (f₂ .fun x)
  ≤⟨ *-mono-≤ ≤-refl (f₁≈f₂ .f≈f x) ⟩
    rational+ ε * 0ℝ
  ≈⟨ *-zeroʳ (rational+ ε) (rational+<∞ ε) ⟩
    0ℝ
  ∎
  where open ≤-Reasoning


------------------------------------------------------------------------------
-- Functoriality properties

map-id : ∀ {ε X} → map {ε}{X} id ≈f id
map-id {ε}{X} .f≈f x = ![ ε ] X .refl {x}

map-∘ : ∀ {ε X Y Z} {f : Y ⇒ Z} {g : X ⇒ Y} →
       map {ε} (f ∘ g) ≈f (map f ∘ map g)
map-∘ {ε}{Z = Z}{f}{g} .f≈f a = ![ ε ] Z .refl {map {ε} f .fun (map {ε} g .fun a)}

weaken : ∀ {ε₁ ε₂ X} → ε₂ ℚ⁺.≤ ε₁ → ![ ε₁ ] X ⇒ ![ ε₂ ] X
weaken ε₂≤ε₁ .fun x = x
weaken ε₂≤ε₁ .non-expansive = *-mono-≤ (rational-mono (ℚ⁺.fog-mono ε₂≤ε₁)) ≤-refl
-- FIXME: weaken is natural, and functorial

------------------------------------------------------------------------------
-- ![_] is a graded exponential comonad with respect to the monoidal
-- !product, so there are quite a few properties to prove for the
-- !natural transformations defined below.

-- FIXME: discard  : ![ 0 ] X ⇒ ⊤ₘ  -- can't do this yet since using ℚ⁺


derelict : ∀ {X} → ![ 1ℚ⁺ ] X ⇒ X
derelict .fun x = x
derelict {X} .non-expansive = ≤-reflexive (≃-sym (*-identityˡ (X .dist _ _)))
-- FIXME: derelict is natural

dig : ∀ {ε₁ ε₂ X} → ![ ε₁ ℚ⁺.* ε₂ ] X ⇒ ![ ε₁ ] (![ ε₂ ] X)
dig .fun x = x
dig {ε₁}{ε₂}{X} .non-expansive {a}{b} =
  begin
    rational+ ε₁ * (rational+ ε₂ * X .dist a b)
  ≈⟨ ≃-sym (*-assoc (rational+ ε₁) (rational+ ε₂) (X .dist a b)) ⟩
    (rational+ ε₁ * rational+ ε₂) * X .dist a b
  ≈⟨ *-cong (rational⁺-* ε₁ ε₂) ≃-refl ⟩
    rational+ (ε₁ ℚ⁺.* ε₂) * X .dist a b
  ∎
  where open ≤-Reasoning
-- FIXME: dig is natural

duplicate : ∀ {ε₁ ε₂ X} → ![ ε₁ ℚ⁺.+ ε₂ ] X ⇒ (![ ε₁ ] X ⊗ ![ ε₂ ] X)
duplicate .fun x = (x , x)
duplicate {ε₁}{ε₂}{X} .non-expansive {a}{b} =
  begin
    (rational+ ε₁ * X .dist a b) + (rational+ ε₂ * X .dist a b)
  ≈⟨ ≃-sym (*-distribʳ-+ (X .dist a b) (rational+ ε₁) (rational+ ε₂)) ⟩
    (rational+ ε₁ + rational+ ε₂) * X .dist a b
  ≈⟨ *-cong (rational⁺-+ ε₁ ε₂) ≃-refl ⟩
    rational+ (ε₁ ℚ⁺.+ ε₂) * X .dist a b
  ≈⟨ ≃-refl ⟩
    dist (![ ε₁ ℚ⁺.+ ε₂ ] X) a b
  ∎
  where open ≤-Reasoning
-- FIXME: duplicate is natural

monoidal : ∀ {ε X Y} → (![ ε ] X ⊗ ![ ε ] Y) ⇒ ![ ε ] (X ⊗ Y)
monoidal .fun (x , y) = x , y
monoidal {ε}{X}{Y} .non-expansive {x₁ , y₁}{x₂ , y₂} =
  begin
    rational+ ε * (X .dist x₁ x₂ + Y .dist y₁ y₂)
  ≈⟨ *-distribˡ-+ (rational+ ε) (X .dist x₁ x₂) (Y .dist y₁ y₂) ⟩
    (rational+ ε * X .dist x₁ x₂) + (rational+ ε * Y .dist y₁ y₂)
  ∎
  where open ≤-Reasoning
-- FIXME: this witnesses ![ ε ] as a monoidal functor:
--   naturality
--   commutes with assoc and swapping
