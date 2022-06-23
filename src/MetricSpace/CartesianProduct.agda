{-# OPTIONS --safe --without-K #-}

module MetricSpace.CartesianProduct where

open import Data.Product using (_,_; _×_)
open import MetricSpace
open import Data.Real.UpperClosed

open MSpc
open _⇒_

_×ₘ_ : MSpc → MSpc → MSpc
(X ×ₘ Y) .Carrier = X .Carrier × Y .Carrier
(X ×ₘ Y) .dist (x₁ , y₁) (x₂ , y₂) = X .dist x₁ x₂ ⊔ Y .dist y₁ y₂
(X ×ₘ Y) .refl = ⊔-least (X .refl) (Y .refl)
(X ×ₘ Y) .sym = ⊔-least (≤-trans (X .sym) ⊔-upper-1) (≤-trans (Y .sym) ⊔-upper-2)
(X ×ₘ Y) .triangle = ⊔-least (≤-trans (X .triangle) (+-mono-≤ ⊔-upper-1 ⊔-upper-1))
                             (≤-trans (Y .triangle) (+-mono-≤ ⊔-upper-2 ⊔-upper-2))

project₁ : ∀ {X Y} → (X ×ₘ Y) ⇒ X
project₁ .fun (x , y) = x
project₁ .non-expansive = ⊔-upper-1

project₂ : ∀ {X Y} → (X ×ₘ Y) ⇒ Y
project₂ .fun (x , y) = y
project₂ .non-expansive = ⊔-upper-2

⟨_,_⟩ : ∀ {X Y Z} → X ⇒ Y → X ⇒ Z → X ⇒ (Y ×ₘ Z)
⟨ f , g ⟩ .fun x = f .fun x , g .fun x
⟨ f , g ⟩ .non-expansive = ⊔-least (f .non-expansive) (g .non-expansive)


-- FIXME: cartesian product equations
