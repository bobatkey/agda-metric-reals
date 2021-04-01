module metric2.convex-alg where

open import Data.Product using (_,_)

open import Data.Rational.Unnormalised as ℚ using () renaming (ℚᵘ to ℚ; 0ℚᵘ to 0ℚ; 1ℚᵘ to 1ℚ)
open import metric2.base

import upper-reals
open import qpos as ℚ⁺ using (ℚ⁺; 1ℚ⁺)

open MSpc

record ℚ⟨0,1⟩ : Set where
  field
    rational : ℚ⁺
    upper    : rational ℚ⁺.< 1ℚ⁺
open ℚ⟨0,1⟩

data _≃_ : ℚ⟨0,1⟩ → ℚ⟨0,1⟩ → Set where
  *≃* : ∀ {q r} → q .rational ℚ⁺.≃ r .rational → q ≃ r

_*_ : ℚ⟨0,1⟩ → ℚ⟨0,1⟩ → ℚ⟨0,1⟩
(q * r) .rational = q .rational ℚ⁺.* r .rational
(q * r) .upper = begin-strict
                   q .rational ℚ⁺.* r .rational
                     <⟨ ℚ⁺.*-mono-< (q .upper) (r .upper) ⟩
                   1ℚ⁺ ℚ⁺.* 1ℚ⁺
                     ≈⟨ ℚ⁺.*-identityʳ 1ℚ⁺ ⟩
                   1ℚ⁺
                 ∎
  where open ℚ⁺.≤-Reasoning

1-_ : ℚ⟨0,1⟩ → ℚ⟨0,1⟩
1- q = {!!}

_/_ : ℚ⟨0,1⟩ → ℚ⟨0,1⟩ → ℚ⟨0,1⟩
(q / r) .rational = q .rational ℚ⁺.* (ℚ⁺.1/ r .rational)
(q / r) .upper = {!!}

module _ (X : MSpc) where

  data term : Set where
    η     : X .Carrier → term
    split : term → ℚ⟨0,1⟩ → term → term

  data within : term → ℚ⁺ → term → Set where
    tm-wk    : ∀ {s t ε₁ ε₂} → ε₁ ℚ⁺.≤ ε₂ → within s ε₁ t → within s ε₂ t
    tm-refl  : ∀ {t ε} → within t ε t
    tm-sym   : ∀ {s t ε} → within s ε t → within t ε s
    tm-trans : ∀ {s t u ε₁ ε₂} → within s ε₁ t → within t ε₂ u → within s (ε₁ ℚ⁺.+ ε₂) u
    tm-arch  : ∀ {s t ε} → (∀ δ → within s (ε ℚ⁺.+ δ) t) → within s ε t
    tm-var   : ∀ {x y ε} → X .dist x y upper-reals.≤ upper-reals.rational+ ε → within (η x) ε (η y)
    tm-idem  : ∀ {t q ε} → within (split t q t) ε t
    tm-assoc : ∀ {s t u q₁ q₂ q₁' q₂' ε} →
                 q₁' ≃ (q₁ * q₂) →
                 q₂' ≃ ((q₁ * (1- q₂)) / (1- (q₁ * q₂))) →
                 within (split (split s q₁ t) q₂ u)
                        ε
                        (split s q₁' (split t q₂' u))
    tm-dist  : ∀ {s₁ s₂ t₁ t₂ ε₁ ε₂ ε q} →
                 within s₁ ε₁ t₁ →
                 within s₂ ε₂ t₂ →
                 ε ℚ⁺.≃ ε₁ ℚ⁺.* q .rational ℚ⁺.+ ε₂ ℚ⁺.* (1- q) .rational →
                 within (split s₁ q s₂) ε (split t₁ q t₂)
    -- FIXME: also add tm-comm ???

  open upper-reals.ℝᵘ

  -- a metric space!
  𝕋 : MSpc
  𝕋 .Carrier = term
  𝕋 .dist s t .contains ε = within s ε t
  𝕋 .dist s t .upper = tm-wk
  𝕋 .dist s t .closed = tm-arch
  𝕋 .refl = record { *≤* = λ _ → tm-refl }
  𝕋 .sym = record { *≤* = λ {ε} y-ε-x → tm-sym y-ε-x }
  𝕋 .triangle = record { *≤* = λ {ε} xy-yz → tm-arch (λ δ → let ε₁ , ε₂ , ε₁+ε₂≤ε+s , p , q = xy-yz δ in
                                                              tm-wk ε₁+ε₂≤ε+s (tm-trans p q)) }

open _⇒_

-- Messy!
unit : ∀ {X} → X ⇒ 𝕋 X
unit .fun x = η x
unit {X} .non-expansive {a}{b} =
  record { *≤* = λ x → tm-var (record { *≤* = λ x₁ → X .dist a b .upper-reals.ℝᵘ.upper (ℚ⁺.r≤r x₁) x }) }

-- FIXME: join

-- FIXME: map

-- FIXME: monoidal

{-
-- Integration is definable for any 𝕋-algebra?



sum : term ℚspc → ℚspc .Carrier
sum t = ?

sum-ne : ∀ {ε s t} → within s ε t → abs (sum s ℚ.- sum t) ℚ.≤ fog ε
-}

  -- axioms:
  -- 1. split x 0 y ≡[ ε ] x -- get rid of this if q ∈ ℚ⟨0,1⟩
  -- 2. split x q x ≡[ ε ] x
  -- 3. split x q y ≡[ ε ] split y (1 - q) x -- could be removed if the focus is on step functions
  -- 4. split (split x q y) q' z ≡[ ε ] split x (q*q') (split y ((q - q*q')/(1 - q*q')) z)   -- as long as q, q' ∈ (0,1)
  -- 5. x₁ ≡[ ε ] x₂ → y₁ ≡[ ε' ] y₂ → split x₁ q y₁ ≡[ ε*q + (1 - q)*ε' ] split x₁ q y₂

  -- This should then give an MSpc with a map (split : ℚ[0,1] → term X ×ₘ term X ⇒ term X)

  -- Goal: to prove that there is a non-expansive function
  --
  --      sum : term ℝspc → ℝspc    (or ℚspc? or any normed ℚ-vector space?)
  --
  -- It should also be possible to create an identity element of `𝒞 (term ℚspc)` (or 𝒞 (term ℝspc))
  --
  -- Then integration is ∫ : (ℝ ⇒ ℝ) → ℝ = λ f → join (𝒞-map (sum ∘ term-map f) identity)

  -- this ought to work for any normed ℚ⟨0,1⟩-vector space that has been completed: anything that we can define 'sum' for.

    -- 𝒞-map (term-map f) identity : 𝒞 (term ℝspc)
    -- 𝒞-map (sum ∘ term-map f) identity : 𝒞 ℝspc
    -- join (𝒞-map (sum ∘ term-map f) identity) : ℝspc

  -- then any element of `𝒞 (term X)` can be used for the "measure"

  -- 𝒫 X = 𝒞 (term X)   -- monad of probability measures; need term and 𝒞 to distribute

  -- if 𝒞 and term are strong monads, then this is a higher order function 𝒫 X ⊗ (X ⊸ 𝕍) ⊸ 𝕍
  -- where X is any metic space
  --   and 𝕍 is any normed ℚ-vector space (or convex set??) that is complete

  -- for step functions:
  --   eval : term X ⊗ ℚ⟨0,1⟩ ⇒ X
  -- presuambly for step functions, the result of the integration needn't be a commutative module


  -- IDEA: what if we combine 'term' and the free ωCPO monad? do we
  -- get recursion + metric reasoning? Probably need some rules to
  -- combine the order with the metric. See the POPL paper by those
  -- people.
