{-# OPTIONS --without-K --allow-unsolved-metas #-}

module metric2.reals where

open import metric2.base
open metric2.base.category
open import metric2.completion renaming (map to 𝒞-map; unit to 𝒞-unit)
open import metric2.rationals
open import metric2.monoidal
open import metric2.terminal
open import metric2.scaling
open import qpos as ℚ⁺ using (ℚ⁺)
open import upper-reals as ℝᵘ using (ℝᵘ)


------------------------------------------------------------------------------
-- the real numbers as the metric completion of the rationals

ℝspc : MSpc
ℝspc = 𝒞 ℚspc

ℝspc[_] : ℚ⁺ → MSpc
ℝspc[ b ] = 𝒞 ℚspc[ b ]

ℝ : Set
ℝ = ℝspc .MSpc.Carrier

ℝ[_] : ℚ⁺ → Set
ℝ[ q ] = ℝspc[ q ] .MSpc.Carrier

------------------------------------------------------------------------------
-- FIXME: order, equality, apartness

_≃_ : ℝ → ℝ → Set
x ≃ y = MSpc._≈_ ℝspc x y

------------------------------------------------------------------------------

-- FIXME: this seems to type check really slowly without no-eta-equality on MSpc and _⇒_
addℝ : (ℝspc ⊗ ℝspc) ⇒ ℝspc
addℝ = 𝒞-map add ∘ monoidal-⊗

negateℝ : ℝspc ⇒ ℝspc
negateℝ = 𝒞-map negate

zeroℝ : ⊤ₘ ⇒ ℝspc
zeroℝ = 𝒞-unit ∘ zero

-- FIXME: now to prove that this gives an abelian group (by abstract
-- nonsense to do with monoidal functors)

-- scaling a real by a positive rational
scale : ∀ q → ![ q ] ℝspc ⇒ ℝspc
scale q = 𝒞-map (ℚ-scale q) ∘ distr q

-- FIXME:
-- 1. multiplication
-- 2. reciprocal

mulℝ : ∀ a b → (![ b ] ℝspc[ a ] ⊗ ![ a ] ℝspc[ b ]) ⇒ ℝspc
mulℝ a b = 𝒞-map (mul a b) ∘ monoidal-⊗ ∘ (distr b ⊗f distr a)

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
bound r = get-bound r , 𝒞-map (clamp (get-bound r)) ._⇒_.fun r

open _⇒_

ℝ-forget : ∀ {q} → ℝ[ q ] → ℝ
ℝ-forget {q} = 𝒞-map (forget q) ._⇒_.fun

bound-eq : ∀ x → ℝ-forget (bound x .proj₂) ≃ x
bound-eq x =
  𝒞-≈ {x = ℝ-forget (bound x .proj₂)} {y = x} λ ε₁ ε₂ →
  begin
     ℝᵘ.rational ℚ.∣ ℝ-forget (bound x .proj₂) .RegFun.rfun ε₁ ℚ.- x .RegFun.rfun ε₂ ∣
  ≡⟨⟩
     ℝᵘ.rational ℚ.∣ forget (get-bound x) .fun (clamp (get-bound x) .fun (x .RegFun.rfun ε₁)) ℚ.- x .RegFun.rfun ε₂ ∣
     -- FIXME: work out what the expression describing the clamped value is
  ≤⟨ {!!} ⟩
     ℝᵘ.rational+ (ε₁ ℚ⁺.+ ε₂)
  ∎
  where open ℝᵘ.≤-Reasoning

{-
mult : ℝ → ℝ → ℝ
mult x y = {!!}
 -- 1. get an approximation of x and y by (.rfun ½)
 -- 2. clamp both
 -- 3. apply the underlying function of mulℝ
-}
