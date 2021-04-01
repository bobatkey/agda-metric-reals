module metric2.scaling where

open import Data.Product using (_,_)
open import metric2.base
open import metric2.monoidal
open import upper-reals
import qpos as ℚ⁺
open ℚ⁺ using (ℚ⁺; 1ℚ⁺)

open MSpc
open _⇒_
open _≈f_

-- A graded comonad, for expressing sensitivity wrt inputs

-- FIXME: ought to be ℚ≥0, or even ℝᵘ (but that isn't a set!)
![_] : ℚ⁺ → MSpc → MSpc
![ ε ] X .Carrier = X .Carrier
![ ε ] X .dist x y = scale ε (X .dist x y)
![ ε ] X .refl = ≤-trans (scale-mono ℚ⁺.≤-refl (X .refl)) scale-0
![ ε ] X .sym = scale-mono ℚ⁺.≤-refl (X .sym)
![ ε ] X .triangle = ≤-trans (scale-mono ℚ⁺.≤-refl (X .triangle)) (≤-reflexive scale-+)

-- FIXME: discard  : ![ 0 ] X ⇒ ⊤ₘ  -- can't do this yet since using ℚ⁺

map : ∀ {ε X Y} → X ⇒ Y → ![ ε ] X ⇒ ![ ε ] Y
map f .fun x = f .fun x
map f .non-expansive = scale-mono ℚ⁺.≤-refl (f .non-expansive)

map-cong : ∀ {ε X Y} {f₁ f₂ : X ⇒ Y} → f₁ ≈f f₂ → map {ε} f₁ ≈f map {ε} f₂
map-cong f₁≈f₂ .f≈f x = ≤-trans (scale-mono ℚ⁺.≤-refl (f₁≈f₂ .f≈f x)) scale-0

-- FIXME: map-id and map-∘

weaken : ∀ {ε₁ ε₂ X} → ε₂ ℚ⁺.≤ ε₁ → ![ ε₁ ] X ⇒ ![ ε₂ ] X
weaken ε₂≤ε₁ .fun x = x
weaken ε₂≤ε₁ .non-expansive = scale-mono ε₂≤ε₁ ≤-refl
-- FIXME: weaken is natural

derelict : ∀ {X} → ![ 1ℚ⁺ ] X ⇒ X
derelict .fun x = x
derelict .non-expansive = 1-scale
-- FIXME: derelict is natural

dig : ∀ {ε₁ ε₂ X} → ![ ε₁ ℚ⁺.* ε₂ ] X ⇒ ![ ε₁ ] (![ ε₂ ] X)
dig .fun x = x
dig .non-expansive = *-scale
-- FIXME: dig is natural

duplicate : ∀ {ε₁ ε₂ X} → ![ ε₁ ℚ⁺.+ ε₂ ] X ⇒ (![ ε₁ ] X ⊗ ![ ε₂ ] X)
duplicate .fun x = (x , x)
duplicate .non-expansive = +-scale
-- FIXME: duplicate is natural

monoidal : ∀ {ε X Y} → (![ ε ] X ⊗ ![ ε ] Y) ⇒ ![ ε ] (X ⊗ Y)
monoidal .fun (x , y) = x , y
monoidal .non-expansive = ≤-reflexive scale-+
-- FIXME: this witnesses ![ ε ] as a monoidal functor:
--   naturality
--   commutes with assoc and swapping
