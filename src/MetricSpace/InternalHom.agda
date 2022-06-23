{-# OPTIONS --without-K --safe #-}

module MetricSpace.InternalHom where

open import Data.Product using (_,_)
open import MetricSpace
open import MetricSpace.MonoidalProduct
open import Data.Real.UpperClosed

open MSpc
open _⇒_

_⊸_ : MSpc → MSpc → MSpc
(X ⊸ Y) .Carrier = X ⇒ Y
(X ⊸ Y) .dist f g = sup (X .Carrier) λ x → Y .dist (f .fun x) (g .fun x)
(X ⊸ Y) .refl = sup-least (λ x → Y .refl)
(X ⊸ Y) .sym = sup-mono-≤ (λ x → x) λ x → Y .sym
(X ⊸ Y) .triangle {f}{g}{h} =
  sup-least λ x → ≤-trans (Y .triangle) (+-mono-≤ (sup-upper x) (sup-upper x))

Λ : ∀ {X Y Z} → (X ⊗ Y) ⇒ Z → X ⇒ (Y ⊸ Z)
Λ f .fun x .fun y = f .fun (x , y)
Λ {X}{Y}{Z} f .fun x .non-expansive {y₁}{y₂} =
  begin
    Z .dist (f .fun (x , y₁)) (f .fun (x , y₂))
      ≤⟨ f .non-expansive ⟩
    (X ⊗ Y) .dist (x , y₁) (x , y₂)
      ≤⟨ +-mono-≤ (X .refl) ≤-refl ⟩
    0ℝ + Y .dist y₁ y₂
      ≈⟨ +-identityˡ (Y .dist y₁ y₂) ⟩
    Y .dist y₁ y₂
  ∎
  where open ≤-Reasoning
Λ {X}{Y}{Z} f .non-expansive {x₁}{x₂}=
  sup-least (λ y → begin
    Z .dist (f .fun (x₁ , y)) (f .fun (x₂ , y))
      ≤⟨ f .non-expansive ⟩
    (X ⊗ Y) .dist (x₁ , y) (x₂ , y)
      ≤⟨ +-mono-≤ ≤-refl (Y .refl) ⟩
    X .dist x₁ x₂ + 0ℝ
      ≈⟨ +-identityʳ (X .dist x₁ x₂) ⟩
    X .dist x₁ x₂
  ∎)
  where open ≤-Reasoning

Λ⁻¹ : ∀ {X Y Z} → X ⇒ (Y ⊸ Z) → (X ⊗ Y) ⇒ Z
Λ⁻¹ f .fun (x , y) = f .fun x .fun y
Λ⁻¹ {X}{Y}{Z} f .non-expansive {x₁ , y₁}{x₂ , y₂} =
  begin
    Z .dist (f .fun x₁ .fun y₁) (f .fun x₂ .fun y₂)
      ≤⟨ Z .triangle ⟩
    Z .dist (f .fun x₁ .fun y₁) (f .fun x₂ .fun y₁) + Z .dist (f .fun x₂ .fun y₁) (f .fun x₂ .fun y₂)
      ≤⟨ +-mono-≤ (sup-upper y₁) ≤-refl ⟩
    (Y ⊸ Z) .dist (f .fun x₁) (f .fun x₂) + Z .dist (f .fun x₂ .fun y₁) (f .fun x₂ .fun y₂)
      ≤⟨ +-mono-≤ (f .non-expansive) (f .fun x₂ .non-expansive) ⟩
    (X ⊗ Y) .dist (x₁ , y₁) (x₂ , y₂)
  ∎
  where open ≤-Reasoning

open MetricSpace.category

eval : ∀ {X Y} → ((X ⊸ Y) ⊗ X) ⇒ Y
eval = Λ⁻¹ id



-- FIXME:
-- 1. _⊸_ is a bifunuctor
-- 2. Λ and Λ⁻¹ are natural
-- 3. Λ and Λ⁻¹ are mutually inverse
