{-# OPTIONS --without-K --safe #-}

module MetricSpace.MonoidalProduct where

open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import MetricSpace
open import MetricSpace.Category
open import MetricSpace.Terminal
open import MetricSpace.CartesianProduct
open import Data.Real.UpperClosed

open MSpc
open _⇒_
open _≈f_

-- FIXME: parameterise this by the norm being used. Construction of
-- the monoidal structure ought to be generic.

_⊗_ : MSpc → MSpc → MSpc
(X ⊗ Y) .Carrier =
  X .Carrier × Y .Carrier
(X ⊗ Y) .dist (x₁ , y₁) (x₂ , y₂) =
  X .dist x₁ x₂ + Y .dist y₁ y₂
(X ⊗ Y) .refl {x , y} =
  begin
    X .dist x x + Y .dist y y
      ≤⟨ +-mono-≤ (X .refl) (Y .refl) ⟩
    0ℝ + 0ℝ
      ≈⟨ +-identityˡ 0ℝ ⟩
    0ℝ
  ∎
  where open ≤-Reasoning
(X ⊗ Y) .sym {x₁ , y₁} {x₂ , y₂} =
  begin
    X .dist x₁ x₂ + Y .dist y₁ y₂
      ≤⟨ +-mono-≤ (X .sym) (Y .sym) ⟩
    X .dist x₂ x₁ + Y .dist y₂ y₁
  ∎
  where open ≤-Reasoning
(X ⊗ Y) .triangle {x₁ , y₁} {x₂ , y₂} {x₃ , y₃} =
  begin
    X .dist x₁ x₃ + Y .dist y₁ y₃
      ≤⟨ +-mono-≤ (X .triangle) (Y .triangle) ⟩
    (X .dist x₁ x₂ + X .dist x₂ x₃) + (Y .dist y₁ y₂ + Y .dist y₂ y₃)
      ≈⟨ +-assoc _ _ _ ⟩
    X .dist x₁ x₂ + (X .dist x₂ x₃ + (Y .dist y₁ y₂ + Y .dist y₂ y₃))
      ≈⟨ +-cong ≃-refl (≃-sym (+-assoc _ _ _)) ⟩
    X .dist x₁ x₂ + ((X .dist x₂ x₃ + Y .dist y₁ y₂) + Y .dist y₂ y₃)
      ≈⟨ +-cong ≃-refl (+-cong (+-comm _ _) ≃-refl) ⟩
    X .dist x₁ x₂ + ((Y .dist y₁ y₂ + X .dist x₂ x₃) + Y .dist y₂ y₃)
      ≈⟨ +-cong ≃-refl (+-assoc _ _ _) ⟩
    X .dist x₁ x₂ + (Y .dist y₁ y₂ + (X .dist x₂ x₃ + Y .dist y₂ y₃))
      ≈⟨ ≃-sym (+-assoc _ _ _) ⟩
    (X .dist x₁ x₂ + Y .dist y₁ y₂) + (X .dist x₂ x₃ + Y .dist y₂ y₃)
  ∎
  where open ≤-Reasoning

≈-⊗ : ∀ {X Y} {x₁ x₂ : X .Carrier} {y₁ y₂ : Y .Carrier} →
      _≈_ X x₁ x₂ → _≈_ Y y₁ y₂ → _≈_ (X ⊗ Y) (x₁ , y₁) (x₂ , y₂)
≈-⊗ {X}{Y}{x₁}{x₂}{y₁}{y₂} x₁≈x₂ y₁≈y₂ =
  begin
    (X ⊗ Y) .dist (x₁ , y₁) (x₂ , y₂)
  ≡⟨⟩
    X .dist x₁ x₂ + Y .dist y₁ y₂
  ≤⟨ +-mono-≤ x₁≈x₂ y₁≈y₂ ⟩
    0ℝ + 0ℝ
  ≈⟨ +-identityʳ 0ℝ ⟩
    0ℝ
  ∎
  where open ≤-Reasoning

_⊗f_ : ∀ {X X' Y Y'} → X ⇒ X' → Y ⇒ Y' → (X ⊗ Y) ⇒ (X' ⊗ Y')
(f ⊗f g) .fun (x , y) = f .fun x , g .fun y
(f ⊗f g) .non-expansive {x₁ , y₁} {x₂ , y₂} = +-mono-≤ (f .non-expansive) (g .non-expansive)

⊗f-cong : ∀ {X X' Y Y'} {f₁ f₂ : X ⇒ X'}{g₁ g₂ : Y ⇒ Y'} →
  f₁ ≈f f₂ → g₁ ≈f g₂ → (f₁ ⊗f g₁) ≈f (f₂ ⊗f g₂)
⊗f-cong f₁≈f₂ g₁≈g₂ .f≈f (x , y) =
  ≤-trans (+-mono-≤ (f₁≈f₂ .f≈f x) (g₁≈g₂ .f≈f y)) (≤-reflexive (+-identityʳ 0ℝ))

-- FIXME: ⊗f preserves composition and identities

⊗f-∘ : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃} →
       (f  : X₂ ⇒ X₃) → (g  : X₁ ⇒ X₂) →
       (f' : Y₂ ⇒ Y₃) → (g' : Y₁ ⇒ Y₂) →
       ((f ∘ g) ⊗f (f' ∘ g')) ≈f ((f ⊗f f') ∘ (g ⊗f g'))
⊗f-∘ {X₃ = X₃}{Y₃ = Y₃} f g f' g' .f≈f (x₁ , y₁) =
  (X₃ ⊗ Y₃) .≈-refl

------------------------------------------------------------------------------
-- From this product to the cartesian one. This could be derived from
-- relationships between the norms used to define them.

⊗⇒× : ∀ {X Y} → (X ⊗ Y) ⇒ (X ×ₘ Y)
⊗⇒× .fun xy = xy
⊗⇒× .non-expansive = ⊔-least (+-increasingʳ _ _) (+-increasingˡ _ _)

-- FIXME: this is natural, and preserves assoc, units, etc.

------------------------------------------------------------------------------
-- Associativity
⊗-assoc : ∀ {X Y Z} → (X ⊗ (Y ⊗ Z)) ⇒ ((X ⊗ Y) ⊗ Z)
⊗-assoc .fun (x , (y , z)) = ((x , y) , z)
⊗-assoc .non-expansive = ≤-reflexive (+-assoc _ _ _)

⊗-assoc⁻¹ : ∀ {X Y Z} → ((X ⊗ Y) ⊗ Z) ⇒ (X ⊗ (Y ⊗ Z))
⊗-assoc⁻¹ .fun ((x , y) , z) = (x , (y , z))
⊗-assoc⁻¹ .non-expansive = ≤-reflexive (≃-sym (+-assoc _ _ _))

-- FIXME: mutually inverse

-- FIXME: pentagon

------------------------------------------------------------------------------
-- Swapping
⊗-symmetry : ∀ {X Y} → (X ⊗ Y) ⇒ (Y ⊗ X)
⊗-symmetry .fun (x , y) = y , x
⊗-symmetry .non-expansive = ≤-reflexive (+-comm _ _)

------------------------------------------------------------------------------
-- Units

left-unit : ∀ {X} → (⊤ₘ ⊗ X) ⇒ X
left-unit .fun (tt , x) = x
left-unit .non-expansive = ≤-reflexive (≃-sym (+-identityˡ _))

left-unit⁻¹ : ∀ {X} → X ⇒ (⊤ₘ ⊗ X)
left-unit⁻¹ .fun x = (tt , x)
left-unit⁻¹ .non-expansive = ≤-reflexive (+-identityˡ _)

module _ where

  left-unit-iso₁ : ∀ {X} → (left-unit ∘ left-unit⁻¹) ≈f (id {X})
  left-unit-iso₁ {X} .f≈f a = X .≈-refl

  left-unit-iso₂ : ∀ {X} → (left-unit⁻¹ ∘ left-unit) ≈f (id {⊤ₘ ⊗ X})
  left-unit-iso₂ {X} .f≈f (tt , a) = ≈-⊗ {⊤ₘ} {X} (⊤ₘ .≈-refl) (X .≈-refl)

-- FIXME: define right-unit

-- interaction with associativity
