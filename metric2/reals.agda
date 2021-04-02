module metric2.reals where

open import metric2.base
open import metric2.rationals
open import metric2.monoidal
open import metric2.terminal
open import Data.Rational.Unnormalised using () renaming (0ℚᵘ to 0ℚ)
open import metric2.completion renaming (map to 𝒞-map; unit to 𝒞-unit)

------------------------------------------------------------------------------
-- the real numbers as the completion of the rationals

ℝspc : MSpc
ℝspc = 𝒞 ℚspc

------------------------------------------------------------------------------
open metric2.base.category

-- FIXME: this seems to type check really slowly without no-eta-equality on MSpc
addℝ : (ℝspc ⊗ ℝspc) ⇒ ℝspc
addℝ = 𝒞-map add ∘ monoidal-⊗

negateℝ : ℝspc ⇒ ℝspc
negateℝ = 𝒞-map negate

zeroℝ : ⊤ₘ ⇒ ℝspc
zeroℝ = 𝒞-unit ∘ const 0ℚ

-- FIXME: now to prove that this gives an abelian group (by abstract
-- nonsense to do with monoidal functors)
