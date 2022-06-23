module MetricSpace.ConvexAlgebras where

open import Data.Product using (_,_; Σ-syntax; proj₁; proj₂; _×_)
open import Data.Unit using (tt)
import Data.Real.UpperClosed as ℝᵘ
import Data.Integer as ℤ
import Data.Nat as ℕ
open import Data.Rational.Unnormalised as ℚ using () renaming (ℚᵘ to ℚ; 0ℚᵘ to 0ℚ; 1ℚᵘ to 1ℚ)
import Data.Rational.Unnormalised.Properties as ℚ
open import MetricSpace

open import Data.Rational.Unnormalised.Positive as ℚ⁺ using (ℚ⁺; 1ℚ⁺)

open MSpc

record ℚ⟨0,1⟩ : Set where
  field
    num : ℚ
    0<n : 0ℚ ℚ.< num
    n<1 : num ℚ.< 1ℚ
  pos : ℚ⁺
  pos = ℚ⁺.⟨ num , ℚ.positive 0<n ⟩
open ℚ⟨0,1⟩

½ : ℚ⟨0,1⟩
½ .num = ℚ.½
½ .0<n = ℚ.*<* (ℤ.+<+ (ℕ.s≤s ℕ.z≤n))
½ .n<1 = ℚ.*<* (ℤ.+<+ (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))

record _≃_ (q r : ℚ⟨0,1⟩) : Set where
  field
    n≃n : q .num ℚ.≃ r .num

_*_ : ℚ⟨0,1⟩ → ℚ⟨0,1⟩ → ℚ⟨0,1⟩
(q * r) .num = q .num ℚ.* r .num
(q * r) .0<n =
  begin-strict
    0ℚ
  ≈⟨ ℚ.≃-sym (ℚ.*-zeroˡ (r .num)) ⟩
    0ℚ ℚ.* r .num
  <⟨ ℚ.*-monoˡ-<-pos (ℚ.positive (r .0<n)) (q .0<n) ⟩
    q .num ℚ.* r .num
  ∎
  where open ℚ.≤-Reasoning
(q * r) .n<1 =
  begin-strict
    q .num ℚ.* r .num
  <⟨ ℚ.*-monoˡ-<-pos (ℚ.positive (r .0<n)) (q .n<1) ⟩ -- ℚ.*-monoˡ-≤-nonNeg (ℚ.nonNegative (r .0≤n)) (q .n≤1) ⟩
    1ℚ ℚ.* r .num
  <⟨ ℚ.*-monoʳ-<-pos {r = 1ℚ} tt (r .n<1) ⟩
    1ℚ ℚ.* 1ℚ
  ≈⟨ ℚ.*-identityˡ 1ℚ ⟩
    1ℚ
  ∎
  where open ℚ.≤-Reasoning

1-_ : ℚ⟨0,1⟩ → ℚ⟨0,1⟩
(1- q) .num = 1ℚ ℚ.- q .num
(1- q) .0<n =
  begin-strict
    0ℚ
  ≈⟨ ℚ.≃-sym (ℚ.+-inverseʳ (q .num)) ⟩
    q .num ℚ.- q .num
  <⟨ ℚ.+-monoˡ-< (ℚ.- q .num) (q .n<1) ⟩
    1ℚ ℚ.- q .num
  ∎
  where open ℚ.≤-Reasoning
(1- q) .n<1 =
  begin-strict
    1ℚ ℚ.- q .num
  <⟨ ℚ.+-monoʳ-< 1ℚ (ℚ.neg-mono-< (q .0<n)) ⟩
    1ℚ ℚ.- 0ℚ
  ≈⟨ ℚ.+-congʳ 1ℚ ε⁻¹≈ε ⟩
    1ℚ ℚ.+ 0ℚ
  ≈⟨ ℚ.+-identityʳ 1ℚ ⟩
    1ℚ
  ∎
  where open ℚ.≤-Reasoning
        open import Algebra.Properties.Group (ℚ.+-0-group)

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
    tm-var   : ∀ {x y ε} → X .dist x y ℝᵘ.≤ ℝᵘ.rational+ ε → within (η x) ε (η y)
    tm-idem  : ∀ {t q ε} → within (split t q t) ε t
    tm-assoc : ∀ {s t u q₁ q₂ q₁' q₂' ε} →
                 q₁' ≃ (q₁ * q₂) →
                 ((1- (q₁ * q₂)) * q₂') ≃ (q₁ * (1- q₂)) →
                 within (split (split s q₁ t) q₂ u)
                        ε
                        (split s q₁' (split t q₂' u))
    tm-dist  : ∀ {s₁ s₂ t₁ t₂ ε₁ ε₂ ε q} →
                 within s₁ ε₁ t₁ →
                 within s₂ ε₂ t₂ →
                 -- this is what gives us the Kantorovich metric between them
                 ε ℚ⁺.≃ ε₁ ℚ⁺.* pos q ℚ⁺.+ ε₂ ℚ⁺.* pos (1- q) →
                 within (split s₁ q s₂) ε (split t₁ q t₂)
    -- FIXME: also add tm-comm ??? and tm-zero
    -- is the only difference between probability distributions and step functions commutativity?

  open ℝᵘ

  -- a metric space!
  𝕋 : MSpc
  𝕋 .Carrier = term
  𝕋 .dist s t = inf (Σ[ ε ∈ ℚ⁺ ] (within s ε t)) (λ p → rational+ (p .proj₁))
  𝕋 .refl =
    ≤-trans
      (inf-greatest (λ i → inf-lower ((i .proj₁) , tm-refl)))
      (≤-reflexive (≃-sym (approx 0ℝ)))
  𝕋 .sym = inf-greatest (λ p → inf-lower (p .proj₁ , tm-sym (p .proj₂)))
  𝕋 .triangle {s}{t}{u} =
    begin
      𝕋 .dist s u
    ≤⟨ inf-greatest (λ { ((ε₁ , s-t)  , (ε₂ , t-u)) → ≤-trans (inf-lower (ε₁ ℚ⁺.+ ε₂ , tm-trans s-t t-u)) (≤-reflexive (≃-sym (rational⁺-+ ε₁ ε₂))) }) ⟩
      inf ((Σ[ ε ∈ ℚ⁺ ] (within s ε t)) × (Σ[ ε ∈ ℚ⁺ ] (within t ε u))) (λ p → rational+ (p .proj₁ .proj₁) + rational+ (p .proj₂ .proj₁))
    ≈⟨ inf-+ ⟩
      𝕋 .dist s t + 𝕋 .dist t u
    ∎
    where open ≤-Reasoning

open _⇒_

open ℝᵘ

-- Messy!
unit : ∀ {X} → X ⇒ 𝕋 X
unit .fun x = η x
unit {X} .non-expansive {a}{b} =
  ≤-trans
    (inf-greatest (λ i → inf-lower ((i .proj₁) , (tm-var (i .proj₂)))))
    (≤-reflexive (≃-sym (approx (dist X a b))))

{-
-- FIXME: join
join : ∀ {X} → 𝕋 (𝕋 X) ⇒ 𝕋 X
join .fun = {!!}
join .non-expansive = {!!}
-}

-- FIXME: map

-- FIXME: monoidal

-- FIXME: completion distributes over 𝕋

open import Data.Nat using (ℕ; zero; suc)
open import MetricSpace.Rationals

step-identity : ℕ → ℚ → ℚ → term ℚspc
step-identity ℕ.zero q a = η q
step-identity (suc n) q a =
  let a = ℚ.½ ℚ.* a in
  split (step-identity n (q ℚ.- a) a) ½ (step-identity n (q ℚ.+ a) a)
-- then start it with ½

-- _ = {!step-identity 3 ℚ.½ ℚ.½!}

-- Then define 'uniform : 𝒞 (term ℚspc)' as a regular function


sum : term ℚspc → ℚspc .Carrier
sum (η x) = x
sum (split t₁ q t₂) = q .num ℚ.* sum t₁ ℚ.+ (1ℚ ℚ.- q .num) ℚ.* sum t₂

-- _ = {! sum (step-identity 5 ℚ.½ ℚ.½) !}

-- and sum is non-expansive


sum-ne : ∀ {ε s t} → within ℚspc s ε t → ℚ.∣ sum s ℚ.- sum t ∣ ℚ.≤ ℚ⁺.fog ε
sum-ne (tm-wk x p) = {!!}
sum-ne tm-refl = {!!}
sum-ne (tm-sym p) = {!!}
sum-ne (tm-trans p p₁) = {!!}
sum-ne (tm-arch x) = {!!}
sum-ne (tm-var x) = {!!}
sum-ne tm-idem = {!!}
sum-ne (tm-assoc x x₁) = {!!}
sum-ne (tm-dist p p₁ eq) = {!!}


{-
-- Integration is definable for any 𝕋-algebra?
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
