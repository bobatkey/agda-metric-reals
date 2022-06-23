{-# OPTIONS --without-K --allow-unsolved-metas #-}

module MetricSpace.CauchyReals where

open import Level using (0ℓ)
open import MetricSpace
open import MetricSpace.Category
open import MetricSpace.Completion renaming (map to 𝒞-map; unit to 𝒞-unit; map-cong to 𝒞-map-cong; map-∘ to 𝒞-map-∘; map-id to 𝒞-map-id)
open import MetricSpace.Rationals
open import MetricSpace.MonoidalProduct
open import MetricSpace.Terminal
open import MetricSpace.Scaling
open import Data.Rational.Unnormalised.Positive as ℚ⁺ using (ℚ⁺)
open import Algebra
open import Data.Product using (_,_; Σ-syntax)
open import Data.Rational.Unnormalised as ℚ using () renaming (ℚᵘ to ℚ)
import Data.Rational.Unnormalised.Properties as ℚ
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Real.UpperClosed as ℝᵘ using (ℝᵘ)
open import Relation.Nullary
open import Relation.Binary using (IsEquivalence; Setoid)
--open import Relation.Binary using (tri<; tri≈; tri>)


------------------------------------------------------------------------------
-- the real numbers as the metric completion of the rationals

ℝspc : MSpc
ℝspc = 𝒞 ℚspc

ℝspc[_] : ℚ⁺ → MSpc
ℝspc[ b ] = 𝒞 ℚspc[ b ]

ℝspc[_⟩ : ℚ⁺ → MSpc
ℝspc[ a ⟩ = 𝒞 ℚspc[ a ⟩

ℝ : Set
ℝ = ℝspc .MSpc.Carrier

ℝ[_] : ℚ⁺ → Set
ℝ[ q ] = ℝspc[ q ] .MSpc.Carrier

------------------------------------------------------------------------------

_≃_ : ℝ → ℝ → Set
x ≃ y = MSpc._≈_ ℝspc x y

≃-refl : ∀ {x} → x ≃ x
≃-refl {x} = MSpc.≈-refl ℝspc {x}

≃-sym : ∀ {x y} → x ≃ y → y ≃ x
≃-sym {x}{y} = MSpc.≈-sym ℝspc {x} {y}

≃-trans : ∀ {x y z} → x ≃ y → y ≃ z → x ≃ z
≃-trans {x}{y}{z} = MSpc.≈-trans ℝspc {x} {y} {z}

≃-isEquivalence : IsEquivalence _≃_
≃-isEquivalence .IsEquivalence.refl {x} = ≃-refl {x}
≃-isEquivalence .IsEquivalence.sym {x} {y} = ≃-sym {x} {y}
≃-isEquivalence .IsEquivalence.trans {x} {y} {z} = ≃-trans {x} {y} {z}

≃-setoid : Setoid 0ℓ 0ℓ
≃-setoid .Setoid.Carrier = ℝ
≃-setoid .Setoid._≈_ = _≃_
≃-setoid .Setoid.isEquivalence = ≃-isEquivalence

------------------------------------------------------------------------------
-- Arithmetic as morphisms in Metric Spaces

-- FIXME: this seems to type check really slowly without no-eta-equality on MSpc and _⇒_
addℝ : (ℝspc ⊗ ℝspc) ⇒ ℝspc
addℝ = 𝒞-map add ∘ monoidal-⊗

negateℝ : ℝspc ⇒ ℝspc
negateℝ = 𝒞-map negate

zeroℝ : ⊤ₘ ⇒ ℝspc
zeroℝ = 𝒞-unit ∘ zero

-- FIXME: now to prove that this gives an abelian group. This is true
-- for any monoid + monoidal functor, and should probably rely on
-- results from the agda-categories library. AFAICT (2021-12-01) I
-- don't think this result is in the agda-categories library.
addℝ-comm : (addℝ ∘ ⊗-symmetry) ≈f addℝ
addℝ-comm =
  begin
    addℝ ∘ ⊗-symmetry
  ≡⟨⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ⊗-symmetry
  ≈˘⟨ assoc (𝒞-map add) monoidal-⊗ ⊗-symmetry ⟩
    𝒞-map add ∘ (monoidal-⊗ ∘ ⊗-symmetry)
  ≈⟨ ∘-cong (≈f-isEquivalence .IsEquivalence.refl) monoidal-symmetry ⟩
    𝒞-map add ∘ (𝒞-map ⊗-symmetry ∘ monoidal-⊗)
  ≈⟨ assoc (𝒞-map add) (𝒞-map ⊗-symmetry) monoidal-⊗  ⟩
    (𝒞-map add ∘ 𝒞-map ⊗-symmetry) ∘ monoidal-⊗
  ≈˘⟨ ∘-cong 𝒞-map-∘ (≈f-isEquivalence .IsEquivalence.refl) ⟩
    𝒞-map (add ∘ ⊗-symmetry) ∘ monoidal-⊗
  ≈⟨ ∘-cong (𝒞-map-cong add-comm) (≈f-isEquivalence .IsEquivalence.refl) ⟩
    𝒞-map add ∘ monoidal-⊗
  ≡⟨⟩
    addℝ
  ∎
  where open import Relation.Binary.Reasoning.Setoid ≈f-setoid
        open import Relation.Binary using (IsEquivalence; Setoid)

addℝ-assoc : (addℝ ∘ (addℝ ⊗f id) ∘ ⊗-assoc) ≈f (addℝ ∘ (id ⊗f addℝ))
addℝ-assoc =
  begin
    addℝ ∘ (addℝ ⊗f id) ∘ ⊗-assoc
  ≡⟨⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ((𝒞-map add ∘ monoidal-⊗) ⊗f id) ∘ ⊗-assoc
  ≈˘⟨ ∘-cong refl (∘-cong (⊗f-cong refl (identityˡ id)) refl) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ((𝒞-map add ∘ monoidal-⊗) ⊗f (id ∘ id)) ∘ ⊗-assoc
  ≈˘⟨ ∘-cong refl (∘-cong (⊗f-cong refl (∘-cong 𝒞-map-id refl)) refl) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ((𝒞-map add ∘ monoidal-⊗) ⊗f (𝒞-map id ∘ id)) ∘ ⊗-assoc
  ≈⟨ ∘-cong refl (∘-cong (⊗f-∘ (𝒞-map add) monoidal-⊗ (𝒞-map id) id) refl) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ((𝒞-map add ⊗f 𝒞-map id) ∘ (monoidal-⊗ ⊗f id)) ∘ ⊗-assoc
  ≈⟨ assoc (𝒞-map add ∘ monoidal-⊗) ((𝒞-map add ⊗f 𝒞-map id) ∘ (monoidal-⊗ ⊗f id)) ⊗-assoc ⟩
    ((𝒞-map add ∘ monoidal-⊗) ∘ (𝒞-map add ⊗f 𝒞-map id) ∘ (monoidal-⊗ ⊗f id)) ∘ ⊗-assoc
  ≈⟨ ∘-cong (assoc _ _ _) refl ⟩
    (((𝒞-map add ∘ monoidal-⊗) ∘ (𝒞-map add ⊗f 𝒞-map id)) ∘ (monoidal-⊗ ⊗f id)) ∘ ⊗-assoc
  ≈˘⟨ ∘-cong (∘-cong (assoc _ _ _) refl) refl ⟩
    ((𝒞-map add ∘ monoidal-⊗ ∘ (𝒞-map add ⊗f 𝒞-map id)) ∘ (monoidal-⊗ ⊗f id)) ∘ ⊗-assoc
  ≈⟨ ∘-cong (∘-cong (∘-cong refl (monoidal-natural add id)) refl) refl ⟩
    ((𝒞-map add ∘ 𝒞-map (add ⊗f id) ∘ monoidal-⊗) ∘ (monoidal-⊗ ⊗f id)) ∘ ⊗-assoc
  ≈⟨ ∘-cong (∘-cong (assoc _ _ _) refl) refl ⟩
    (((𝒞-map add ∘ 𝒞-map (add ⊗f id)) ∘ monoidal-⊗) ∘ (monoidal-⊗ ⊗f id)) ∘ ⊗-assoc
  ≈⟨ ∘-cong (sym (assoc _ _ _)) refl ⟩
    ((𝒞-map add ∘ 𝒞-map (add ⊗f id)) ∘ monoidal-⊗ ∘ (monoidal-⊗ ⊗f id)) ∘ ⊗-assoc
  ≈⟨ sym (assoc _ _ _) ⟩
    (𝒞-map add ∘ 𝒞-map (add ⊗f id)) ∘ (monoidal-⊗ ∘ (monoidal-⊗ ⊗f id)) ∘ ⊗-assoc
  ≈⟨ ∘-cong (sym 𝒞-map-∘) (sym (assoc _ _ _)) ⟩
    𝒞-map (add ∘ (add ⊗f id)) ∘ (monoidal-⊗ ∘ (monoidal-⊗ ⊗f id) ∘ ⊗-assoc)
  ≈⟨ ∘-cong refl monoidal-assoc ⟩
    𝒞-map (add ∘ (add ⊗f id)) ∘ 𝒞-map ⊗-assoc ∘ monoidal-⊗ ∘ (id ⊗f monoidal-⊗)
  ≈⟨ assoc _ _ _ ⟩
    (𝒞-map (add ∘ (add ⊗f id)) ∘ 𝒞-map ⊗-assoc) ∘ monoidal-⊗ ∘ (id ⊗f monoidal-⊗)
  ≈⟨ ∘-cong (sym 𝒞-map-∘) refl ⟩
    𝒞-map ((add ∘ (add ⊗f id)) ∘ ⊗-assoc) ∘ monoidal-⊗ ∘ (id ⊗f monoidal-⊗)
  ≈⟨ ∘-cong (𝒞-map-cong (sym (assoc _ _ _))) refl ⟩
    𝒞-map (add ∘ (add ⊗f id) ∘ ⊗-assoc) ∘ monoidal-⊗ ∘ (id ⊗f monoidal-⊗)
  ≈⟨ ∘-cong (𝒞-map-cong add-assoc) refl ⟩
    𝒞-map (add ∘ (id ⊗f add)) ∘ monoidal-⊗ ∘ (id ⊗f monoidal-⊗)
  ≈⟨ ∘-cong 𝒞-map-∘ refl ⟩
    (𝒞-map add ∘ 𝒞-map (id ⊗f add)) ∘ monoidal-⊗ ∘ (id ⊗f monoidal-⊗)
  ≈⟨ assoc _ _ _ ⟩
    ((𝒞-map add ∘ 𝒞-map (id ⊗f add)) ∘ monoidal-⊗) ∘ (id ⊗f monoidal-⊗)
  ≈⟨ ∘-cong (sym (assoc _ _ _)) refl ⟩
    (𝒞-map add ∘ 𝒞-map (id ⊗f add) ∘ monoidal-⊗) ∘ (id ⊗f monoidal-⊗)
  ≈⟨ ∘-cong (∘-cong refl (sym (monoidal-natural id add))) refl ⟩
    (𝒞-map add ∘ monoidal-⊗ ∘ (𝒞-map id ⊗f 𝒞-map add)) ∘ (id ⊗f monoidal-⊗)
  ≈⟨ ∘-cong (assoc _ _ _) refl ⟩
    ((𝒞-map add ∘ monoidal-⊗) ∘ (𝒞-map id ⊗f 𝒞-map add)) ∘ (id ⊗f monoidal-⊗)
  ≈⟨ sym (assoc _ _ _) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ (𝒞-map id ⊗f 𝒞-map add) ∘ (id ⊗f monoidal-⊗)
  ≈⟨ ∘-cong refl (sym (⊗f-∘ (𝒞-map id) id (𝒞-map add) monoidal-⊗)) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ((𝒞-map id ∘ id) ⊗f (𝒞-map add ∘ monoidal-⊗))
  ≈⟨ ∘-cong refl (⊗f-cong (∘-cong 𝒞-map-id refl) refl) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ((id ∘ id) ⊗f (𝒞-map add ∘ monoidal-⊗))
  ≈⟨ ∘-cong refl (⊗f-cong (identityˡ id) refl) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ (id ⊗f (𝒞-map add ∘ monoidal-⊗))
  ≡⟨⟩
    addℝ ∘ (id ⊗f addℝ)
  ∎
  where open import Relation.Binary.Reasoning.Setoid ≈f-setoid
        open import Relation.Binary using (IsEquivalence; Setoid)
        refl : ∀ {X Y} {f : X ⇒ Y} → f ≈f f
        refl = ≈f-isEquivalence .IsEquivalence.refl
        sym : ∀ {X Y} {f g : X ⇒ Y} → f ≈f g → g ≈f f
        sym = ≈f-isEquivalence .IsEquivalence.sym

-- This proof is very simple, but very long!
addℝ-identityˡ : (addℝ ∘ (zeroℝ ⊗f id) ∘ left-unit⁻¹) ≈f id
addℝ-identityˡ =
  begin
    addℝ ∘ (zeroℝ ⊗f id) ∘ left-unit⁻¹
  ≡⟨⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ((𝒞-unit ∘ zero) ⊗f id) ∘ left-unit⁻¹
  ≈⟨ ∘-cong refl (∘-cong (⊗f-cong unit-natural refl) refl) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ((𝒞-map zero ∘ 𝒞-unit) ⊗f id) ∘ left-unit⁻¹
  ≈˘⟨ ∘-cong refl (∘-cong (⊗f-cong refl (identityˡ id)) refl) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ((𝒞-map zero ∘ 𝒞-unit) ⊗f (id ∘ id)) ∘ left-unit⁻¹
  ≈˘⟨ ∘-cong refl (∘-cong (⊗f-cong refl (∘-cong 𝒞-map-id refl)) refl) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ((𝒞-map zero ∘ 𝒞-unit) ⊗f (𝒞-map id ∘ id)) ∘ left-unit⁻¹
  ≈⟨ ∘-cong refl (∘-cong (⊗f-∘ (𝒞-map zero) 𝒞-unit (𝒞-map id) id) refl) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ ((𝒞-map zero ⊗f 𝒞-map id) ∘ (𝒞-unit ⊗f id)) ∘ left-unit⁻¹
  ≈⟨ assoc (𝒞-map add ∘ monoidal-⊗) ((𝒞-map zero ⊗f 𝒞-map id) ∘ (𝒞-unit ⊗f id)) left-unit⁻¹ ⟩
    ((𝒞-map add ∘ monoidal-⊗) ∘ (𝒞-map zero ⊗f 𝒞-map id) ∘ (𝒞-unit ⊗f id)) ∘ left-unit⁻¹
  ≈⟨ ∘-cong (assoc (𝒞-map add ∘ monoidal-⊗) (𝒞-map zero ⊗f 𝒞-map id) (𝒞-unit ⊗f id)) refl ⟩
    (((𝒞-map add ∘ monoidal-⊗) ∘ (𝒞-map zero ⊗f 𝒞-map id)) ∘ (𝒞-unit ⊗f id)) ∘ left-unit⁻¹
  ≈˘⟨ ∘-cong (∘-cong (assoc (𝒞-map add) monoidal-⊗ (𝒞-map zero ⊗f 𝒞-map id)) refl) refl ⟩
    ((𝒞-map add ∘ monoidal-⊗ ∘ (𝒞-map zero ⊗f 𝒞-map id)) ∘ (𝒞-unit ⊗f id)) ∘ left-unit⁻¹
  ≈⟨ ∘-cong (∘-cong (∘-cong refl (monoidal-natural zero id)) refl) refl ⟩
    ((𝒞-map add ∘ 𝒞-map (zero ⊗f id) ∘ monoidal-⊗) ∘ (𝒞-unit ⊗f id)) ∘ left-unit⁻¹
  ≈⟨ ∘-cong (∘-cong (assoc (𝒞-map add) (𝒞-map (zero ⊗f id)) monoidal-⊗) refl) refl ⟩
    (((𝒞-map add ∘ 𝒞-map (zero ⊗f id)) ∘ monoidal-⊗) ∘ (𝒞-unit ⊗f id)) ∘ left-unit⁻¹
  ≈˘⟨ ∘-cong (∘-cong (∘-cong 𝒞-map-∘ refl) refl) refl ⟩
    ((𝒞-map (add ∘ (zero ⊗f id)) ∘ monoidal-⊗) ∘ (𝒞-unit ⊗f id)) ∘ left-unit⁻¹
  ≈˘⟨ ∘-cong (assoc (𝒞-map (add ∘ (zero ⊗f id))) monoidal-⊗ (𝒞-unit ⊗f id)) refl ⟩
    (𝒞-map (add ∘ (zero ⊗f id)) ∘ monoidal-⊗ ∘ (𝒞-unit ⊗f id)) ∘ left-unit⁻¹
  ≈⟨ ∘-cong (∘-cong refl monoidal-left-unit) refl ⟩
    (𝒞-map (add ∘ (zero ⊗f id)) ∘ 𝒞-map left-unit⁻¹ ∘ left-unit) ∘ left-unit⁻¹
  ≈⟨ ∘-cong (assoc (𝒞-map (add ∘ (zero ⊗f id))) (𝒞-map left-unit⁻¹) left-unit) refl ⟩
    ((𝒞-map (add ∘ (zero ⊗f id)) ∘ 𝒞-map left-unit⁻¹) ∘ left-unit) ∘ left-unit⁻¹
  ≈˘⟨ ∘-cong (∘-cong 𝒞-map-∘ refl) refl ⟩
    (𝒞-map ((add ∘ (zero ⊗f id)) ∘ left-unit⁻¹) ∘ left-unit) ∘ left-unit⁻¹
  ≈˘⟨ assoc (𝒞-map ((add ∘ (zero ⊗f id)) ∘ left-unit⁻¹)) left-unit left-unit⁻¹ ⟩
    𝒞-map ((add ∘ (zero ⊗f id)) ∘ left-unit⁻¹) ∘ left-unit ∘ left-unit⁻¹
  ≈⟨ ∘-cong (𝒞-map-cong (sym (assoc add (zero ⊗f id) left-unit⁻¹))) left-unit-iso₁ ⟩
    𝒞-map (add ∘ (zero ⊗f id) ∘ left-unit⁻¹) ∘ id
  ≈⟨ ∘-cong (𝒞-map-cong add-identityˡ) refl ⟩
    𝒞-map id ∘ id
  ≈⟨ ∘-cong 𝒞-map-id refl ⟩
    id ∘ id
  ≈⟨ identityˡ id ⟩
    id
  ∎
  where open import Relation.Binary.Reasoning.Setoid ≈f-setoid
        open import Relation.Binary using (IsEquivalence; Setoid)
        refl : ∀ {X Y} {f : X ⇒ Y} → f ≈f f
        refl = ≈f-isEquivalence .IsEquivalence.refl
        sym : ∀ {X Y} {f g : X ⇒ Y} → f ≈f g → g ≈f f
        sym = ≈f-isEquivalence .IsEquivalence.sym

addℝ-inverse : (addℝ ∘ (id ⊗f negateℝ) ∘ (derelict ⊗f derelict) ∘ duplicate) ≈f (zeroℝ ∘ discard)
addℝ-inverse =
  begin
    addℝ ∘ (id ⊗f negateℝ) ∘ (derelict ⊗f derelict) ∘ duplicate
  ≡⟨⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ (id ⊗f 𝒞-map negate) ∘ (derelict ⊗f derelict) ∘ duplicate
  ≈⟨ ∘-cong refl (∘-cong (⊗f-cong (sym 𝒞-map-id) refl) refl) ⟩
    (𝒞-map add ∘ monoidal-⊗) ∘ (𝒞-map id ⊗f 𝒞-map negate) ∘ (derelict ⊗f derelict) ∘ duplicate
  ≈⟨ assoc _ _ _ ⟩
    ((𝒞-map add ∘ monoidal-⊗) ∘ (𝒞-map id ⊗f 𝒞-map negate)) ∘ (derelict ⊗f derelict) ∘ duplicate
  ≈⟨ ∘-cong (sym (assoc _ _ _)) refl ⟩
    (𝒞-map add ∘ monoidal-⊗ ∘ (𝒞-map id ⊗f 𝒞-map negate)) ∘ (derelict ⊗f derelict) ∘ duplicate
  ≈⟨ ∘-cong (∘-cong refl (monoidal-natural id negate)) refl ⟩
    (𝒞-map add ∘ 𝒞-map (id ⊗f negate) ∘ monoidal-⊗) ∘ (derelict ⊗f derelict) ∘ duplicate
  ≈⟨ {!!} ⟩ -- FIXME: need to prove more properties of ![_] and its interaction with 𝒞
    zeroℝ ∘ discard
  ∎
  where open import Relation.Binary.Reasoning.Setoid ≈f-setoid
        open import Relation.Binary using (IsEquivalence; Setoid)
        refl : ∀ {X Y} {f : X ⇒ Y} → f ≈f f
        refl = ≈f-isEquivalence .IsEquivalence.refl
        sym : ∀ {X Y} {f g : X ⇒ Y} → f ≈f g → g ≈f f
        sym = ≈f-isEquivalence .IsEquivalence.sym


------------------------------------------------------------------------------
-- Arithmetic operations as plain functions

-- FIXME: rename these to remove the ℝ suffixes

ℚ→ℝ : ℚ → ℝ
ℚ→ℝ q = 𝒞-unit ._⇒_.fun q

_+ℝ_ : ℝ → ℝ → ℝ
x +ℝ y = addℝ ._⇒_.fun (x , y)

-ℝ_ : ℝ → ℝ
-ℝ_ x = negateℝ ._⇒_.fun x

0ℝ : ℝ
0ℝ = zeroℝ ._⇒_.fun tt

_-ℝ_ : ℝ → ℝ → ℝ
x -ℝ y = x +ℝ (-ℝ y)

------------------------------------------------------------------------------
-- Properties of _+_ and -_

+ℝ-cong : Congruent₂ _≃_ _+ℝ_ -- ∀ {x₁ x₂ y₁ y₂} → x₁ ≃ x₂ → y₁ ≃ y₂ → (x₁ +ℝ y₁) ≃ (x₂ +ℝ y₂)
+ℝ-cong {x₁}{x₂}{y₁}{y₂} x₁≃x₂ y₁≃y₂ =
  _⇒_.cong addℝ {x₁ , y₁} {x₂ , y₂}
                 (≈-⊗ {ℝspc}{ℝspc} {x₁}{x₂}{y₁}{y₂} x₁≃x₂ y₁≃y₂)

-ℝ-cong : Congruent₁ _≃_ (-ℝ_)
-ℝ-cong {x₁}{x₂} x₁≃x₂ =
  _⇒_.cong negateℝ {x₁} {x₂} x₁≃x₂

+ℝ-assoc : ∀ x y z → ((x +ℝ y) +ℝ z) ≃ (x +ℝ (y +ℝ z))
+ℝ-assoc x y z = addℝ-assoc ._≈f_.f≈f (x , (y , z))

+ℝ-comm : ∀ x y → (x +ℝ y) ≃ (y +ℝ x)
+ℝ-comm x y = addℝ-comm ._≈f_.f≈f (y , x)

+ℝ-identityˡ : ∀ x → (0ℝ +ℝ x) ≃ x
+ℝ-identityˡ x = addℝ-identityˡ ._≈f_.f≈f x

+ℝ-identityʳ : ∀ x → (x +ℝ 0ℝ) ≃ x
+ℝ-identityʳ x =
  begin
    x +ℝ 0ℝ
  ≈⟨ +ℝ-comm x 0ℝ ⟩
    0ℝ +ℝ x
  ≈⟨ +ℝ-identityˡ x ⟩
    x
  ∎
  where open import Relation.Binary.Reasoning.Setoid ≃-setoid

+-identity : Identity _≃_ 0ℝ _+ℝ_
+-identity = +ℝ-identityˡ , +ℝ-identityʳ

+-inverseʳ : RightInverse _≃_ 0ℝ -ℝ_ _+ℝ_
+-inverseʳ x = addℝ-inverse ._≈f_.f≈f x

+-inverseˡ : LeftInverse _≃_ 0ℝ -ℝ_ _+ℝ_
+-inverseˡ x =
  begin
    (-ℝ x) +ℝ x  ≈⟨ +ℝ-comm (-ℝ x) x ⟩
    x +ℝ (-ℝ x)  ≈⟨ +-inverseʳ x ⟩
    0ℝ           ∎
  where open import Relation.Binary.Reasoning.Setoid ≃-setoid

+-inverse : Inverse _≃_ 0ℝ -ℝ_ _+ℝ_
+-inverse = +-inverseˡ , +-inverseʳ

------------------------------------------------------------------------------
-- Packaging up the proofs of algeraic properties

+-isMagma : IsMagma _≃_ _+ℝ_
+-isMagma = record { isEquivalence = ≃-isEquivalence ; ∙-cong = λ {x₁}{x₂}{y₁}{y₂} → +ℝ-cong {x₁}{x₂}{y₁}{y₂} }

+-isSemigroup : IsSemigroup _≃_ _+ℝ_
+-isSemigroup = record { isMagma = +-isMagma ; assoc = +ℝ-assoc }

+-isCommutativeSemigroup : IsCommutativeSemigroup _≃_ _+ℝ_
+-isCommutativeSemigroup = record { isSemigroup = +-isSemigroup ; comm = +ℝ-comm }

+-0-isMonoid : IsMonoid _≃_ _+ℝ_ 0ℝ
+-0-isMonoid = record { isSemigroup = +-isSemigroup ; identity = +-identity }

+-0-isCommutativeMonoid : IsCommutativeMonoid _≃_ _+ℝ_ 0ℝ
+-0-isCommutativeMonoid = record { isMonoid = +-0-isMonoid ; comm = +ℝ-comm }

+-0-isGroup : IsGroup _≃_ _+ℝ_ 0ℝ (-ℝ_)
+-0-isGroup = record { isMonoid = +-0-isMonoid ; inverse = +-inverse ; ⁻¹-cong = λ {x₁}{x₂} → -ℝ-cong {x₁}{x₂} }

+-0-isAbelianGroup : IsAbelianGroup _≃_ _+ℝ_ 0ℝ (-ℝ_)
+-0-isAbelianGroup = record { isGroup = +-0-isGroup ; comm = +ℝ-comm }

+-0-AbelianGroup : AbelianGroup 0ℓ 0ℓ
+-0-AbelianGroup = record { isAbelianGroup = +-0-isAbelianGroup }

-- FIXME: bundles



------------------------------------------------------------------------------
-- Order and apartness

-- FIXME: this is unfinished

module _ where

  open RegFun

  0≤ℝ : ℝ → Set
  0≤ℝ x = ∀ ε → ℚ.- ℚ⁺.fog ε ℚ.≤ x .RegFun.rfun ε

  -- https://github.com/coq-community/corn/blob/master/reals/fast/CRGroupOps.v#L177
  -- 0≤ℝ-cong : ∀ {x y} → x ≃ y → 0≤ℝ x → 0≤ℝ y
  -- 0≤ℝ-cong {x} {y} x≃y 0≤x ε = {!!}

  --     with ℚ.<-cmp (x .rfun ε) (y .rfun ε)
  -- ... | tri< x⟨ε⟩<y⟨ε⟩ _ _ =
  --   begin
  --     ℚ.- ℚ⁺.fog ε
  --   ≤⟨ 0≤x ε ⟩
  --     x .rfun ε
  --   <⟨ x⟨ε⟩<y⟨ε⟩ ⟩
  --     y .rfun ε
  --   ∎
  --   where open ℚ.≤-Reasoning
  -- ... | tri≈ _ x⟨ε⟩≈y⟨ε⟩ _ =
  --   begin
  --     ℚ.- ℚ⁺.fog ε
  --   ≤⟨ 0≤x ε ⟩
  --     x .rfun ε
  --   ≈⟨ x⟨ε⟩≈y⟨ε⟩ ⟩
  --     y .rfun ε
  --   ∎
  --   where open ℚ.≤-Reasoning
  -- ... | tri> _ _ y⟨ε⟩<x⟨ε⟩ =
  --   begin
  --     ℚ.- ℚ⁺.fog ε
  --   ≤⟨ {!!} ⟩
  --     y .rfun ε
  --   ∎
  --   where open ℚ.≤-Reasoning

  -- -ε ≤ x⟨ε⟩
  -- | yε - xε | ≤ 2ε
  -- yε < xε
  -- ==> xε - yε ≤ 2ε
  -- ==> xε - 2ε ≤ yε
  --

  -- ≈-𝒞 {ℚspc} {x}{y} x≃y ε ε :  difference between x(ε) and y(ε) is less than (ε + ε)
  -- otherwise, x .rfun ε + (ε + ε) ≤ y .rfun ε
  -- so ε ≤ y .rfun ε and so - ε ≤ y .rfun ε

-- “Not greater than”
_≤ℝ_ : ℝ → ℝ → Set
x ≤ℝ y = 0≤ℝ (y -ℝ x)

≤ℝ-refl : ∀ x → x ≤ℝ x
≤ℝ-refl x ε = {!!}

0<ℝ : ℝ → Set
0<ℝ x = Σ[ ε ∈ ℚ⁺ ] (𝒞-unit ._⇒_.fun (ℚ⁺.fog ε) ≤ℝ x )

-- “Greater than”
_<ℝ_ : ℝ → ℝ → Set
x <ℝ y = 0<ℝ (y -ℝ x)

-- Apartness
_#ℝ_ : ℝ → ℝ → Set
x #ℝ y = x <ℝ y ⊎ y <ℝ x

-- FIXME: axioms for apartness

-- FIXME: prove that the distance function on the reals is really the
-- absolute value of the difference. This would require a mapping of
-- the metric space reals into the upper reals.

{-
module _ where

  open import upper-reals
  open upper-reals.ℝᵘ

  to-upper-real : ℝ → ℝᵘ
  to-upper-real x .contains q = {!x ≤ℝ (ℝ→ℚ q)!}
  to-upper-real x .upper = {!!}
  to-upper-real x .closed = {!!}
-}

------------------------------------------------------------------------------
-- Multiplication and reciprocal

-- scaling a real by a positive rational
scale : ∀ q → ![ q ] ℝspc ⇒ ℝspc
scale q = 𝒞-map (ℚ-scale q) ∘ distr q

-- Fully "metrised" versions of multiplication and reciprocal

mulℝ : ∀ a b → (![ b ] ℝspc[ a ] ⊗ ![ a ] ℝspc[ b ]) ⇒ ℝspc[ a ℚ⁺.* b ]
mulℝ a b = 𝒞-map (mul a b) ∘ monoidal-⊗ ∘ (distr b ⊗f distr a)

reciprocalℝ : ∀ a → ![ ℚ⁺.1/ (a ℚ⁺.* a) ] ℝspc[ a ⟩ ⇒ ℝspc
reciprocalℝ a = 𝒞-map (recip a) ∘ distr (ℚ⁺.1/ (a ℚ⁺.* a))

------------------------------------------------------------------------------
-- Bounding regular functions

open import Data.Product
import Data.Rational.Unnormalised as ℚ
import Data.Rational.Unnormalised.Properties as ℚ

module _ where
  import Data.Integer as ℤ
  import Data.Nat as ℕ

  0<½ : ℚ.0ℚᵘ ℚ.< ℚ.½
  0<½ = ℚ.*<* (ℤ.+<+ (ℕ.s≤s ℕ.z≤n))

get-bound : ℝ → ℚ⁺
get-bound r =
  ℚ⁺.⟨ (ℚ.∣ r .RegFun.rfun ℚ⁺.½ ∣ ℚ.+ ℚ.½)
     , ℚ.positive
        (begin-strict
           ℚ.0ℚᵘ
         ≤⟨ ℚ.0≤∣p∣ (r .RegFun.rfun ℚ⁺.½) ⟩
           ℚ.∣ r .RegFun.rfun ℚ⁺.½ ∣
         ≈⟨ ℚ.≃-sym (ℚ.+-identityʳ ℚ.∣ r .RegFun.rfun ℚ⁺.½ ∣) ⟩
           ℚ.∣ r .RegFun.rfun ℚ⁺.½ ∣ ℚ.+ ℚ.0ℚᵘ
         <⟨ ℚ.+-mono-≤-< (ℚ.≤-refl {ℚ.∣ r .RegFun.rfun ℚ⁺.½ ∣}) 0<½ ⟩
           ℚ.∣ r .RegFun.rfun ℚ⁺.½ ∣ ℚ.+ ℚ.½
         ∎)
     ⟩
  where open ℚ.≤-Reasoning

bound : ℝ → Σ[ q ∈ ℚ⁺ ] ℝ[ q ]
bound r .proj₁ = get-bound r
bound r .proj₂ = {!!} -- 𝒞-map (clamping.clamp (get-bound r)) ._⇒_.fun r

open _⇒_

ℝ-unbound : ∀ {q} → ℝ[ q ] → ℝ
ℝ-unbound {q} = 𝒞-map (unbound q) .fun

bound-eq : ∀ x → ℝ-unbound (bound x .proj₂) ≃ x
bound-eq x =
  𝒞-≈ {x = ℝ-unbound (bound x .proj₂)} {y = x} λ ε₁ ε₂ →
  begin
     ℝᵘ.rational ℚ.∣ ℝ-unbound (bound x .proj₂) .RegFun.rfun ε₁ ℚ.- x .RegFun.rfun ε₂ ∣
  ≡⟨⟩
     ℝᵘ.rational ℚ.∣ clamping.clamp-v (get-bound x) (x .RegFun.rfun ε₁) ℚ.- x .RegFun.rfun ε₂ ∣
  ≤⟨ {!!} ⟩
     ℝᵘ.rational+ (ε₁ ℚ⁺.+ ε₂)
  ∎
  where open ℝᵘ.≤-Reasoning

_*ℝ_ : ℝ → ℝ → ℝ
_*ℝ_ x y =
  let a , x' = bound x in
  let b , y' = bound y in
  ℝ-unbound (mulℝ a b .fun (x' , y'))

-- TODO:
-- 1. congruence
-- 2. associativity (needs proofs from rationals)
-- 3. distributivity
-- 4. identities
-- 5. zeros

2ℝ : ℝ
2ℝ = ℚ→ℝ (ℚ.1ℚᵘ ℚ.+ ℚ.1ℚᵘ)

4ℝ : ℝ
4ℝ = 2ℝ *ℝ 2ℝ

4ℚ : ℚ
4ℚ = ℚ.1ℚᵘ ℚ.+ ℚ.1ℚᵘ ℚ.+ ℚ.1ℚᵘ ℚ.+ ℚ.1ℚᵘ

module _ where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  _ :  4ℝ .RegFun.rfun ℚ⁺.½ ≡ 4ℚ
  _ = refl

------------------------------------------------------------------------
-- TODO: reciprocal

{- If a real is greater than 0 by the above definition, then we can
   use the ε from that to bound it from underneath. Then apply the
   reciprocal on the rationals. -}

------------------------------------------------------------------------
-- TODO: Alternating decreasing series

-- If we have:
--    a series      a : ℕ → ℚ
--    limit is 0:   ∀ ε → Σ[ n ∈ ℕ ] (∣ a n ∣ ≤ ε)
--    alternating:  ???
--    decreasing:   ∀ i → ∣ a (suc i) ∣ < ∣ a i ∣

-- define x(ε) = sum(modulus(ε), a)
--   then prove that this is a regular function

-- and then prove that it gives us the infinite sum??
