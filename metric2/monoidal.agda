{-# OPTIONS --without-K --safe #-}

module metric2.monoidal where

open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import metric2.base
open import metric2.terminal
open import upper-reals

open MSpc
open _⇒_
open _≈f_

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

_⊗f_ : ∀ {X X' Y Y'} → X ⇒ X' → Y ⇒ Y' → (X ⊗ Y) ⇒ (X' ⊗ Y')
(f ⊗f g) .fun (x , y) = f .fun x , g .fun y
(f ⊗f g) .non-expansive {x₁ , y₁} {x₂ , y₂} = +-mono-≤ (f .non-expansive) (g .non-expansive)

⊗f-cong : ∀ {X X' Y Y'} {f₁ f₂ : X ⇒ X'}{g₁ g₂ : Y ⇒ Y'} →
  f₁ ≈f f₂ → g₁ ≈f g₂ → (f₁ ⊗f g₁) ≈f (f₂ ⊗f g₂)
⊗f-cong f₁≈f₂ g₁≈g₂ .f≈f (x , y) =
  ≤-trans (+-mono-≤ (f₁≈f₂ .f≈f x) (g₁≈g₂ .f≈f y)) (≤-reflexive (+-identityʳ 0ℝ))

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
swap : ∀ {X Y} → (X ⊗ Y) ⇒ (Y ⊗ X)
swap .fun (x , y) = y , x
swap .non-expansive = ≤-reflexive (+-comm _ _)

------------------------------------------------------------------------------
-- Units

left-unit : ∀ {X} → (⊤ₘ ⊗ X) ⇒ X
left-unit .fun (tt , x) = x
left-unit .non-expansive = ≤-reflexive (≃-sym (+-identityˡ _))

left-unit⁻¹ : ∀ {X} → X ⇒ (⊤ₘ ⊗ X)
left-unit⁻¹ .fun x = (tt , x)
left-unit⁻¹ .non-expansive = ≤-reflexive (+-identityˡ _)

-- FIXME: define right-unit

-- interaction with associativity
