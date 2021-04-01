module metric2.terminal where

open import Data.Unit using (⊤; tt)
open import metric2.base
open import upper-reals

open MSpc
open _⇒_
open _≈f_

⊤ₘ : MSpc
⊤ₘ .Carrier = ⊤
⊤ₘ .dist tt tt = 0ℝ
⊤ₘ .refl = ≤-refl
⊤ₘ .sym = ≤-refl
⊤ₘ .triangle = ≤-reflexive (≃-sym (+-identityˡ 0ℝ))

discard : ∀ {X} → X ⇒ ⊤ₘ
discard .fun _ = tt
discard .non-expansive = 0-least _

discard-unique : ∀ {X} {f : X ⇒ ⊤ₘ} → f ≈f discard
discard-unique .f≈f a = ≤-refl
