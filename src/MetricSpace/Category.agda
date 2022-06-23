{-# OPTIONS --without-K --safe #-}

module MetricSpace.Category where

open import MetricSpace
open import Data.Real.UpperClosed

open MSpc
open _⇒_
open _≈f_

id : ∀ {X} → X ⇒ X
id .fun x = x
id .non-expansive = ≤-refl

infixr 9 _∘_

_∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
(f ∘ g) .fun x = f .fun (g .fun x)
(f ∘ g) .non-expansive = ≤-trans (f .non-expansive) (g .non-expansive)

∘-cong : ∀ {X Y Z}{f₁ f₂ : Y ⇒ Z}{g₁ g₂ : X ⇒ Y} →
        f₁ ≈f f₂ → g₁ ≈f g₂ →
        (f₁ ∘ g₁) ≈f (f₂ ∘ g₂)
∘-cong {X}{Y}{Z}{f₁}{f₂}{g₁}{g₂} f₁≈f₂ g₁≈g₂ .f≈f a =
  Z .≈-trans (f₁≈f₂ .f≈f (g₁ .fun a)) (cong f₂ (g₁≈g₂ .f≈f a))

identityˡ : ∀ {X Y}(f : X ⇒ Y) → (f ∘ id) ≈f f
identityˡ {X}{Y} f .f≈f a = Y .refl

identityʳ : ∀ {X Y}(f : X ⇒ Y) → (id ∘ f) ≈f f
identityʳ {X}{Y} f .f≈f a = Y .refl

assoc : ∀ {W X Y Z}(f : Y ⇒ Z)(g : X ⇒ Y)(h : W ⇒ X) →
        (f ∘ g ∘ h) ≈f ((f ∘ g) ∘ h)
assoc {Z = Z} f g h .f≈f w = Z .refl
