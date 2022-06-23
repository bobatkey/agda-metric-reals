{-# OPTIONS --without-K --safe #-}

module MetricSpace.Discrete where

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import MetricSpace
open import Data.Real.UpperClosed

open MSpc
open _⇒_

module _ (A : Setoid 0ℓ 0ℓ) where
  module A = Setoid A

  open _≤_
  open import Data.Product using (_,_; proj₁; proj₂)
  open import Data.Unit using (tt)

  discrete : MSpc
  discrete .Carrier = A.Carrier
  discrete .dist a b = inf (a A.≈ b) (λ _ → 0ℝ)
  discrete .refl = inf-lower A.refl
  discrete .sym = inf-greatest (λ y≈x → inf-lower (A.sym y≈x))
  discrete .triangle .*≤* h s =
    -- FIXME: prove enough things about inf that this can be done abstractly
    let ε₁ , ε₂ , _ , x≈y∋ε₁ , y≈z∋ε₂ = h s in
    let x≈y , _ = x≈y∋ε₁ s in
    let y≈z , _ = y≈z∋ε₂ s in
    A.trans x≈y y≈z , tt

  eq-is-0 : ∀ x y → x A.≈ y → discrete .dist x y ≃ 0ℝ
  eq-is-0 x y x≈y .proj₁ = inf-lower x≈y
  eq-is-0 x y x≈y .proj₂ = 0-least _

  neq-is-∞ : ∀ x y → ¬ (x A.≈ y) → discrete .dist x y ≃ ∞
  neq-is-∞ x y x≉y .proj₁ = ∞-greatest _
  neq-is-∞ x y x≉y .proj₂ = inf-greatest (λ x≈y → ⊥-elim (x≉y x≈y))

-- FIXME: prove that all non-expansive functions from a connected
-- space to a discrete space are constant

-- FIXME: all Setoid morphisms become non-expansive functions, so we
-- have a full and faithful functor Setoids -> MSpc
