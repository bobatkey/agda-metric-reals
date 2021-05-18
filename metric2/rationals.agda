{-# OPTIONS --without-K --allow-unsolved-metas #-}

module metric2.rationals where

open import Data.Product using (proj₁; proj₂; _,_; Σ-syntax)
open import Data.Rational.Unnormalised as ℚ using () renaming (ℚᵘ to ℚ; 0ℚᵘ to 0ℚ; 1ℚᵘ to 1ℚ)
import Data.Rational.Unnormalised.Properties as ℚ
open import metric2.base
open import upper-reals

open MSpc
open _⇒_
open _≈f_

private
  dist-sym : ∀ x y → ℚ.∣ x ℚ.- y ∣ ℚ.≃ ℚ.∣ y ℚ.- x ∣
  dist-sym x y =
    begin-equality
      ℚ.∣ x ℚ.- y ∣
    ≈⟨ ℚ.≃-sym (ℚ.∣-p∣≃∣p∣ (x ℚ.- y)) ⟩
      ℚ.∣ ℚ.- (x ℚ.- y) ∣
    ≈⟨ ℚ.∣-∣-cong (⁻¹-anti-homo-∙ x (ℚ.- y)) ⟩
      ℚ.∣ ℚ.- (ℚ.- y) ℚ.- x ∣
    ≈⟨ ℚ.∣-∣-cong (ℚ.+-congˡ (ℚ.- x) (⁻¹-involutive y)) ⟩
      ℚ.∣ y ℚ.- x ∣
    ∎
    where open ℚ.≤-Reasoning
          open import Algebra.Properties.AbelianGroup ℚ.+-0-abelianGroup

ℚspc : MSpc
ℚspc .Carrier = ℚ
ℚspc .dist x y = rational ℚ.∣ x ℚ.- y ∣
ℚspc .refl {x} =
  begin
    rational ℚ.∣ x ℚ.- x ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-inverseʳ x)) ⟩
    rational ℚ.∣ 0ℚ ∣
  ≈⟨ rational-cong (ℚ.0≤p⇒∣p∣≃p ℚ.≤-refl) ⟩
    rational 0ℚ
  ≈⟨ rational-0 ⟩
    0ℝ
  ∎
  where open ≤-Reasoning
ℚspc .sym {x}{y} =
  begin
    rational ℚ.∣ x ℚ.- y ∣
  ≈⟨ rational-cong (dist-sym x y) ⟩
    rational ℚ.∣ y ℚ.- x ∣
  ∎
  where open ≤-Reasoning
ℚspc .triangle {x}{y}{z} =
  begin
    rational ℚ.∣ x ℚ.- z ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.+-identityʳ (x ℚ.- z)))) ⟩
    rational (ℚ.∣ (x ℚ.- z) ℚ.+ 0ℚ ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.+-congʳ (x ℚ.- z) (ℚ.+-inverseˡ y)))) ⟩
    rational (ℚ.∣ (x ℚ.- z) ℚ.+ (ℚ.- y ℚ.+ y) ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ-interchange x (ℚ.- z) (ℚ.- y) y)) ⟩
    rational (ℚ.∣ (x ℚ.- y) ℚ.+ ((ℚ.- z) ℚ.+ y) ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congʳ (x ℚ.- y) (ℚ.+-comm (ℚ.- z) y))) ⟩
    rational (ℚ.∣ (x ℚ.- y) ℚ.+ (y ℚ.- z) ∣)
  ≤⟨ rational-mono (ℚ.∣p+q∣≤∣p∣+∣q∣ (x ℚ.- y) (y ℚ.- z)) ⟩
    rational (ℚ.∣ x ℚ.- y ∣ ℚ.+ ℚ.∣ y ℚ.- z ∣)
  ≈⟨ ≃-sym (rational-+ ℚ.∣ x ℚ.- y ∣ ℚ.∣ y ℚ.- z ∣ (ℚ.0≤∣p∣ (x ℚ.- y)) (ℚ.0≤∣p∣ (y ℚ.- z))) ⟩
    rational ℚ.∣ x ℚ.- y ∣ + rational ℚ.∣ y ℚ.- z ∣
  ∎
  where open ≤-Reasoning

ℚspc-≈ : ∀ {q r} → q ℚ.≃ r → _≈_ ℚspc q r
ℚspc-≈ {q}{r} q≃r =
  begin
    rational ℚ.∣ q ℚ.- r ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congˡ (ℚ.- r) q≃r)) ⟩
    rational ℚ.∣ r ℚ.- r ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-inverseʳ r)) ⟩
    rational ℚ.∣ 0ℚ ∣
  ≈⟨ rational-cong (ℚ.0≤p⇒∣p∣≃p ℚ.≤-refl) ⟩
    rational 0ℚ
  ≈⟨ rational-0 ⟩
    0ℝ
  ∎
  where open ≤-Reasoning

open import metric2.monoidal
open import metric2.terminal
open import metric2.internal-hom
open import qpos as ℚ⁺ using (ℚ⁺)
open metric2.base.category

const : ℚ → ⊤ₘ ⇒ ℚspc
const q .fun _ = q
const q .non-expansive = ℚspc .refl {q}

------------------------------------------------------------------------------
-- ℚspc is a commutative monoid object in the category of metric
-- spaces and non-expansive maps

zero : ⊤ₘ ⇒ ℚspc
zero = const 0ℚ

add : (ℚspc ⊗ ℚspc) ⇒ ℚspc
add .fun (a , b) = a ℚ.+ b
add .non-expansive {a₁ , b₁}{a₂ , b₂} =
  begin
    rational ℚ.∣ a₁ ℚ.+ b₁ ℚ.- (a₂ ℚ.+ b₂) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congʳ (a₁ ℚ.+ b₁) (ℚ.≃-sym (⁻¹-∙-comm a₂ b₂)))) ⟩
    rational ℚ.∣ a₁ ℚ.+ b₁ ℚ.+ (ℚ.- a₂ ℚ.- b₂) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ-interchange a₁ b₁ (ℚ.- a₂) (ℚ.- b₂))) ⟩
    rational ℚ.∣ (a₁ ℚ.- a₂) ℚ.+ (b₁ ℚ.- b₂) ∣
  ≤⟨ rational-mono (ℚ.∣p+q∣≤∣p∣+∣q∣ (a₁ ℚ.- a₂) (b₁ ℚ.- b₂)) ⟩
    rational (ℚ.∣ a₁ ℚ.- a₂ ∣ ℚ.+ ℚ.∣ b₁ ℚ.- b₂ ∣)
  ≈⟨ ≃-sym (rational-+ ℚ.∣ a₁ ℚ.- a₂ ∣ ℚ.∣ b₁ ℚ.- b₂ ∣ (ℚ.0≤∣p∣ (a₁ ℚ.- a₂)) (ℚ.0≤∣p∣ (b₁ ℚ.- b₂))) ⟩
    rational ℚ.∣ a₁ ℚ.- a₂ ∣ + rational ℚ.∣ b₁ ℚ.- b₂ ∣
  ≈⟨ ≃-refl ⟩
    dist (ℚspc ⊗ ℚspc) (a₁ , b₁) (a₂ , b₂)
  ∎
  where open ≤-Reasoning
        open import Algebra.Properties.AbelianGroup (ℚ.+-0-abelianGroup)

add-identityˡ : (add ∘ (zero ⊗f id) ∘ left-unit⁻¹) ≈f id
add-identityˡ .f≈f a = ℚspc-≈ (ℚ.+-identityˡ a)

add-comm : (add ∘ ⊗-symmetry) ≈f add
add-comm .f≈f (a , b) = ℚspc-≈ (ℚ.+-comm b a)

add-assoc : (add ∘ (add ⊗f id) ∘ ⊗-assoc) ≈f (add ∘ (id ⊗f add))
add-assoc .f≈f (a , (b , c)) = ℚspc-≈ (ℚ.+-assoc a b c)

------------------------------------------------------------------------------
-- Negation, so we have a (graded) abelian group object
open import metric2.scaling

negate : ℚspc ⇒ ℚspc
negate .fun a = ℚ.- a
negate .non-expansive {a}{b} =
  begin
    rational ℚ.∣ ℚ.- a ℚ.- ℚ.- b ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (⁻¹-∙-comm a (ℚ.- b))) ⟩
    rational ℚ.∣ ℚ.- (a ℚ.- b) ∣
  ≈⟨ rational-cong (ℚ.∣-p∣≃∣p∣ (a ℚ.- b)) ⟩
    dist ℚspc a b
  ∎
  where open ≤-Reasoning
        open import Algebra.Properties.AbelianGroup (ℚ.+-0-abelianGroup)

-- ![ 2 ] ℚspc → ℚspc
add-inverse : (add ∘ (id ⊗f negate) ∘ (derelict ⊗f derelict) ∘ duplicate) ≈f (zero ∘ discard)
add-inverse .f≈f q = ℚspc-≈ (ℚ.+-inverseʳ q)


------------------------------------------------------------------------------
-- Multiplication by a "scalar"

-- FIXME: make this work for any q : ℚ; need scaling to work for non-negative rationals
ℚ-scale : (q : ℚ⁺) → ![ q ] ℚspc ⇒ ℚspc
ℚ-scale q .fun a = ℚ⁺.fog q ℚ.* a
ℚ-scale q .non-expansive {a}{b} =
  begin
    rational ℚ.∣ ℚ⁺.fog q ℚ.* a ℚ.- ℚ⁺.fog q ℚ.* b ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congʳ (ℚ⁺.fog q ℚ.* a) (ℚ.neg-distribʳ-* (ℚ⁺.fog q) b))) ⟩
    rational ℚ.∣ ℚ⁺.fog q ℚ.* a ℚ.+ ℚ⁺.fog q ℚ.* (ℚ.- b) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.*-distribˡ-+ (ℚ⁺.fog q) a (ℚ.- b)))) ⟩
    rational ℚ.∣ ℚ⁺.fog q ℚ.* (a ℚ.- b) ∣
  ≈⟨ rational-cong (ℚ.∣p*q∣≃∣p∣*∣q∣ (ℚ⁺.fog q) (a ℚ.- b)) ⟩
    rational (ℚ.∣ ℚ⁺.fog q ∣ ℚ.* ℚ.∣ a ℚ.- b ∣)
  ≈⟨ ≃-sym (rational-* ℚ.∣ ℚ⁺.fog q ∣ ℚ.∣ a ℚ.- b ∣ (ℚ.0≤∣p∣ (ℚ⁺.fog q)) (ℚ.0≤∣p∣ (a ℚ.- b))) ⟩
    rational ℚ.∣ ℚ⁺.fog q ∣ * rational ℚ.∣ a ℚ.- b ∣
  ≈⟨ *-cong (rational-cong (ℚ.0≤p⇒∣p∣≃p (ℚ⁺.fog-nonneg q))) ≃-refl ⟩
    rational+ q * rational ℚ.∣ a ℚ.- b ∣
  ≡⟨⟩
    ![ q ] ℚspc .dist a b
  ∎
  where open ≤-Reasoning

-- FIXME: make this work for any q : ℚ; need scaling to work for non-negative rationals
ℚ-scale2 : (q : ℚ)(ε : ℚ⁺) → ℚ.∣ q ∣ ℚ.≤ ℚ⁺.fog ε → ![ ε ] ℚspc ⇒ ℚspc
ℚ-scale2 q ε ∣q∣≤ε .fun a = q ℚ.* a
ℚ-scale2 q ε ∣q∣≤ε  .non-expansive {a}{b} =
  begin
    rational ℚ.∣ q ℚ.* a ℚ.- q ℚ.* b ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congʳ (q ℚ.* a) (ℚ.neg-distribʳ-* q b))) ⟩
    rational ℚ.∣ q ℚ.* a ℚ.+ q ℚ.* (ℚ.- b) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.*-distribˡ-+ q a (ℚ.- b)))) ⟩
    rational ℚ.∣ q ℚ.* (a ℚ.- b) ∣
  ≈⟨ rational-cong (ℚ.∣p*q∣≃∣p∣*∣q∣ q (a ℚ.- b)) ⟩
    rational (ℚ.∣ q ∣ ℚ.* ℚ.∣ (a ℚ.- b) ∣)
  ≤⟨ rational-mono (ℚ.*-monoˡ-≤-nonNeg (ℚ.∣-∣-nonNeg (a ℚ.- b)) ∣q∣≤ε) ⟩
    rational (ℚ⁺.fog ε ℚ.* ℚ.∣ (a ℚ.- b) ∣)
  ≈⟨ ≃-sym (rational-* (ℚ⁺.fog ε) ℚ.∣ a ℚ.- b ∣ (ℚ⁺.fog-nonneg ε) (ℚ.0≤∣p∣ (a ℚ.- b))) ⟩
    rational+ ε * rational ℚ.∣ (a ℚ.- b) ∣
  ≡⟨⟩
    dist (![ ε ] ℚspc) a b
  ∎
  where open ≤-Reasoning

------------------------------------------------------------------------------
-- Bounded ℚspc

ℚspc[_] : ℚ⁺ → MSpc
ℚspc[ b ] .Carrier = Σ[ q ∈ ℚ ] (ℚ.∣ q ∣ ℚ.≤ ℚ⁺.fog b)
ℚspc[ b ] .dist (x , _) (y , _) = rational ℚ.∣ x ℚ.- y ∣
ℚspc[ b ] .refl {x , _} =
  begin
    rational ℚ.∣ x ℚ.- x ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-inverseʳ x)) ⟩
    rational ℚ.∣ 0ℚ ∣
  ≈⟨ rational-cong (ℚ.0≤p⇒∣p∣≃p ℚ.≤-refl) ⟩
    rational 0ℚ
  ≈⟨ rational-0 ⟩
    0ℝ
  ∎
  where open ≤-Reasoning
ℚspc[ b ] .sym {x , _}{y , _} =
  begin
    rational ℚ.∣ x ℚ.- y ∣
  ≈⟨ rational-cong (ℚ.≃-sym (ℚ.∣-p∣≃∣p∣ (x ℚ.- y))) ⟩
    rational ℚ.∣ ℚ.- (x ℚ.- y) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (⁻¹-anti-homo-∙ x (ℚ.- y))) ⟩
    rational ℚ.∣ ℚ.- (ℚ.- y) ℚ.- x ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congˡ (ℚ.- x) (⁻¹-involutive y))) ⟩
    rational ℚ.∣ y ℚ.- x ∣
  ∎
  where open ≤-Reasoning
        open import Algebra.Properties.AbelianGroup ℚ.+-0-abelianGroup
ℚspc[ b ] .triangle {x , _}{y , _}{z , _} =
  begin
    rational ℚ.∣ x ℚ.- z ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.+-identityʳ (x ℚ.- z)))) ⟩
    rational (ℚ.∣ (x ℚ.- z) ℚ.+ 0ℚ ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.+-congʳ (x ℚ.- z) (ℚ.+-inverseˡ y)))) ⟩
    rational (ℚ.∣ (x ℚ.- z) ℚ.+ (ℚ.- y ℚ.+ y) ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ-interchange x (ℚ.- z) (ℚ.- y) y)) ⟩
    rational (ℚ.∣ (x ℚ.- y) ℚ.+ ((ℚ.- z) ℚ.+ y) ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congʳ (x ℚ.- y) (ℚ.+-comm (ℚ.- z) y))) ⟩
    rational (ℚ.∣ (x ℚ.- y) ℚ.+ (y ℚ.- z) ∣)
  ≤⟨ rational-mono (ℚ.∣p+q∣≤∣p∣+∣q∣ (x ℚ.- y) (y ℚ.- z)) ⟩
    rational (ℚ.∣ x ℚ.- y ∣ ℚ.+ ℚ.∣ y ℚ.- z ∣)
  ≈⟨ ≃-sym (rational-+ ℚ.∣ x ℚ.- y ∣ ℚ.∣ y ℚ.- z ∣ (ℚ.0≤∣p∣ (x ℚ.- y)) (ℚ.0≤∣p∣ (y ℚ.- z))) ⟩
    rational ℚ.∣ x ℚ.- y ∣ + rational ℚ.∣ y ℚ.- z ∣
  ∎
  where open ≤-Reasoning

forget : ∀ b → ℚspc[ b ] ⇒ ℚspc
forget b .fun (q , _) = q
forget b .non-expansive = ≤-refl

open import Data.Sum using (inj₁; inj₂)

lemma : ∀ q b → (ℚ.- (ℚ⁺.fog b)) ℚ.≤ q → q ℚ.≤ ℚ⁺.fog b → ℚ.∣ q ∣ ℚ.≤ ℚ⁺.fog b
lemma q b -b≤q q≤b with ℚ.∣p∣≡p∨∣p∣≡-p q
... | inj₁ ∣q∣≡q =
  begin
    ℚ.∣ q ∣   ≡⟨ ∣q∣≡q ⟩
    q        ≤⟨ q≤b ⟩
    ℚ⁺.fog b ∎
  where open ℚ.≤-Reasoning
... | inj₂ ∣q∣≡-q =
  begin
    ℚ.∣ q ∣             ≡⟨ ∣q∣≡-q ⟩
    ℚ.- q              ≤⟨ ℚ.neg-mono-≤ -b≤q ⟩
    ℚ.- (ℚ.- ℚ⁺.fog b) ≈⟨ ℚ.neg-involutive (ℚ⁺.fog b) ⟩
    ℚ⁺.fog b            ∎
  where open ℚ.≤-Reasoning

lemma2 : ∀ q → 0ℚ ℚ.≤ q → ℚ.- q ℚ.≤ q
lemma2 q 0≤q =
  begin
    ℚ.- q         ≤⟨ ℚ.neg-mono-≤ 0≤q ⟩
    ℚ.- (ℚ.- 0ℚ) ≈⟨ ℚ.neg-involutive 0ℚ ⟩
    0ℚ            ≤⟨ 0≤q ⟩
    q             ∎
  where open ℚ.≤-Reasoning

clamp : ∀ b → ℚspc ⇒ ℚspc[ b ]
clamp b .fun q =
  (q ℚ.⊔ ℚ.- ℚ⁺.fog b) ℚ.⊓ ℚ⁺.fog b ,
  lemma (((q ℚ.⊔ (ℚ.- (ℚ⁺.fog b))) ℚ.⊓ (ℚ⁺.fog b))) b
    (ℚ.⊓-glb (ℚ.p≤q⊔p q (ℚ.- ℚ⁺.fog b))
             (lemma2 (ℚ⁺.fog b) (ℚ⁺.fog-nonneg b)))
    (ℚ.p≤q⇒r⊓p≤q (q ℚ.⊔ (ℚ.- (ℚ⁺.fog b))) ℚ.≤-refl)
  where open ℚ.≤-Reasoning
clamp b .non-expansive {q₁}{q₂} =
  {!!}
  where open ℚ.≤-Reasoning

------------------------------------------------------------------------------
-- Multiplication

multiply : ∀ a b → ![ b ] (ℚspc[ a ]) ⇒ (![ a ] (ℚspc[ b ]) ⊸ ℚspc)
multiply a b .fun (q , ∣q∣≤a) .fun (r , ∣r∣≤b) = q ℚ.* r
multiply a b .fun (q , ∣q∣≤a) .non-expansive {r₁ , ∣r₁∣≤b} {r₂ , ∣r₂∣≤b} =
  begin
    rational ℚ.∣ q ℚ.* r₁ ℚ.- q ℚ.* r₂ ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congʳ (q ℚ.* r₁) (ℚ.neg-distribʳ-* q r₂))) ⟩
    rational ℚ.∣ q ℚ.* r₁ ℚ.+ q ℚ.* (ℚ.- r₂) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.*-distribˡ-+ q r₁ (ℚ.- r₂)))) ⟩
    rational ℚ.∣ q ℚ.* (r₁ ℚ.- r₂) ∣
  ≈⟨ rational-cong (ℚ.∣p*q∣≃∣p∣*∣q∣ q (r₁ ℚ.- r₂)) ⟩
    rational (ℚ.∣ q ∣ ℚ.* ℚ.∣ r₁ ℚ.- r₂ ∣)
  ≈⟨ ≃-sym (rational-* ℚ.∣ q ∣ ℚ.∣ r₁ ℚ.- r₂ ∣ (ℚ.0≤∣p∣ q) (ℚ.0≤∣p∣ (r₁ ℚ.- r₂))) ⟩
    rational (ℚ.∣ q ∣) * rational ℚ.∣ r₁ ℚ.- r₂ ∣
  ≤⟨ *-mono-≤ (rational-mono ∣q∣≤a) ≤-refl ⟩
    rational+ a * rational ℚ.∣ r₁ ℚ.- r₂ ∣
  ∎
  where open ≤-Reasoning
multiply a b .non-expansive {q₁ , ∣q₁∣≤a}{q₂ , ∣q₂∣≤a} =
  sup-least λ { (r , ∣r∣≤b) →
  begin
    rational ℚ.∣ q₁ ℚ.* r ℚ.- q₂ ℚ.* r ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congʳ (q₁ ℚ.* r) (ℚ.neg-distribˡ-* q₂ r))) ⟩
    rational ℚ.∣ q₁ ℚ.* r ℚ.+ (ℚ.- q₂) ℚ.* r ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.*-distribʳ-+ r q₁ (ℚ.- q₂)))) ⟩
    rational ℚ.∣ (q₁ ℚ.- q₂) ℚ.* r ∣
  ≈⟨ rational-cong (ℚ.∣p*q∣≃∣p∣*∣q∣ (q₁ ℚ.- q₂) r) ⟩
    rational (ℚ.∣ q₁ ℚ.- q₂ ∣ ℚ.* ℚ.∣ r ∣)
  ≈⟨ rational-cong (ℚ.*-comm ℚ.∣ q₁ ℚ.- q₂ ∣ ℚ.∣ r ∣) ⟩
    rational (ℚ.∣ r ∣ ℚ.* ℚ.∣ q₁ ℚ.- q₂ ∣)
  ≈⟨ ≃-sym (rational-* ℚ.∣ r ∣ ℚ.∣ q₁ ℚ.- q₂ ∣ (ℚ.0≤∣p∣ r) (ℚ.0≤∣p∣ (q₁ ℚ.- q₂))) ⟩
    rational (ℚ.∣ r ∣) * rational ℚ.∣ q₁ ℚ.- q₂ ∣
  ≤⟨ *-mono-≤ (rational-mono ∣r∣≤b) ≤-refl ⟩
    rational+ b * rational ℚ.∣ q₁ ℚ.- q₂ ∣
  ∎ }
  where open ≤-Reasoning

mul : ∀ a b → (![ b ] (ℚspc[ a ]) ⊗ ![ a ] (ℚspc[ b ])) ⇒ ℚspc
mul a b = Λ⁻¹ (multiply a b)

------------------------------------------------------------------------------
-- Reciprocals

ℚspc[_⟩ : ℚ⁺ → MSpc
ℚspc[ b ⟩ .Carrier = Σ[ q ∈ ℚ ] (ℚ⁺.fog b ℚ.≤ q)
ℚspc[ b ⟩ .dist (x , _) (y , _) = rational ℚ.∣ x ℚ.- y ∣
ℚspc[ b ⟩ .refl {x , _} =
  begin
    rational ℚ.∣ x ℚ.- x ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-inverseʳ x)) ⟩
    rational ℚ.∣ 0ℚ ∣
  ≈⟨ rational-cong (ℚ.0≤p⇒∣p∣≃p ℚ.≤-refl) ⟩
    rational 0ℚ
  ≈⟨ rational-0 ⟩
    0ℝ
  ∎
  where open ≤-Reasoning
ℚspc[ b ⟩ .sym {x , _}{y , _} =
  begin
    rational ℚ.∣ x ℚ.- y ∣
  ≈⟨ rational-cong (ℚ.≃-sym (ℚ.∣-p∣≃∣p∣ (x ℚ.- y))) ⟩
    rational ℚ.∣ ℚ.- (x ℚ.- y) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (⁻¹-anti-homo-∙ x (ℚ.- y))) ⟩
    rational ℚ.∣ ℚ.- (ℚ.- y) ℚ.- x ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congˡ (ℚ.- x) (⁻¹-involutive y))) ⟩
    rational ℚ.∣ y ℚ.- x ∣
  ∎
  where open ≤-Reasoning
        open import Algebra.Properties.AbelianGroup ℚ.+-0-abelianGroup
ℚspc[ b ⟩ .triangle {x , _}{y , _}{z , _} =
  begin
    rational ℚ.∣ x ℚ.- z ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.+-identityʳ (x ℚ.- z)))) ⟩
    rational (ℚ.∣ (x ℚ.- z) ℚ.+ 0ℚ ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.+-congʳ (x ℚ.- z) (ℚ.+-inverseˡ y)))) ⟩
    rational (ℚ.∣ (x ℚ.- z) ℚ.+ (ℚ.- y ℚ.+ y) ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ-interchange x (ℚ.- z) (ℚ.- y) y)) ⟩
    rational (ℚ.∣ (x ℚ.- y) ℚ.+ ((ℚ.- z) ℚ.+ y) ∣)
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-congʳ (x ℚ.- y) (ℚ.+-comm (ℚ.- z) y))) ⟩
    rational (ℚ.∣ (x ℚ.- y) ℚ.+ (y ℚ.- z) ∣)
  ≤⟨ rational-mono (ℚ.∣p+q∣≤∣p∣+∣q∣ (x ℚ.- y) (y ℚ.- z)) ⟩
    rational (ℚ.∣ x ℚ.- y ∣ ℚ.+ ℚ.∣ y ℚ.- z ∣)
  ≈⟨ ≃-sym (rational-+ ℚ.∣ x ℚ.- y ∣ ℚ.∣ y ℚ.- z ∣ (ℚ.0≤∣p∣ (x ℚ.- y)) (ℚ.0≤∣p∣ (y ℚ.- z))) ⟩
    rational ℚ.∣ x ℚ.- y ∣ + rational ℚ.∣ y ℚ.- z ∣
  ∎
  where open ≤-Reasoning

module _ where
  open import Data.Integer as ℤ
  open import Data.Nat as ℕ
  open import Relation.Nullary
  open import Data.Unit using (tt)

  nonzero : ∀ a q → ℚ⁺.fog a ℚ.≤ q → ℤ.∣ ℚ.↥ q ∣ ℚ.≢0
  nonzero a q a≤q = ℚ.p≄0⇒∣↥p∣≢0 q λ q≃0 →
    ℚ⁺.fog-not≤0 a (begin ℚ⁺.fog a ≤⟨ a≤q ⟩ q ≈⟨ q≃0 ⟩ 0ℚ ∎)
    where open ℚ.≤-Reasoning

recip : ∀ a → ![ ℚ⁺.1/ (a ℚ⁺.* a) ] ℚspc[ a ⟩ ⇒ ℚspc
recip a .fun (q , a≤q) = ℚ.1/_ q {nonzero a q a≤q}
recip a .non-expansive {q , a≤q} {r , a≤r} =
  begin
    rational ℚ.∣ ℚ.1/ q ℚ.- ℚ.1/ r ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-cong (ℚ.≃-sym (ℚ.*-identityˡ (ℚ.1/ q))) (ℚ.-‿cong (ℚ.≃-sym (ℚ.*-identityˡ (ℚ.1/ r)))))) ⟩
    rational ℚ.∣ (1ℚ ℚ.* ℚ.1/ q) ℚ.- (1ℚ ℚ.* ℚ.1/ r) ∣
  ≈⟨ ≃-sym (rational-cong (ℚ.∣-∣-cong (ℚ.+-cong (ℚ.*-cong (ℚ.*-inverseʳ r {r≢0}) (ℚ.≃-refl {ℚ.1/ q}))
                                     (ℚ.-‿cong (ℚ.*-cong (ℚ.*-inverseʳ q {q≢0}) (ℚ.≃-refl {ℚ.1/ r})))))) ⟩
    rational ℚ.∣ ((r ℚ.* ℚ.1/ r) ℚ.* ℚ.1/ q) ℚ.- ((q ℚ.* ℚ.1/ q) ℚ.* ℚ.1/ r) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-cong (ℚ.≃-refl {(r ℚ.* ℚ.1/ r) ℚ.* ℚ.1/ q})
                                        (ℚ.-‿cong (ℚ.*-assoc q (ℚ.1/ q) (ℚ.1/ r))))) ⟩
    rational ℚ.∣ ((r ℚ.* ℚ.1/ r) ℚ.* ℚ.1/ q) ℚ.- (q ℚ.* (ℚ.1/ q ℚ.* ℚ.1/ r)) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-cong (ℚ.≃-refl {(r ℚ.* ℚ.1/ r) ℚ.* ℚ.1/ q})
                                         (ℚ.-‿cong (ℚ.*-cong (ℚ.≃-refl {q}) (ℚ.*-comm (ℚ.1/ q) (ℚ.1/ r)))))) ⟩
    rational ℚ.∣ ((r ℚ.* ℚ.1/ r) ℚ.* ℚ.1/ q) ℚ.- (q ℚ.* (ℚ.1/ r ℚ.* ℚ.1/ q)) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-cong (ℚ.≃-refl {(r ℚ.* ℚ.1/ r) ℚ.* ℚ.1/ q})
                                        (ℚ.neg-distribˡ-* q (ℚ.1/ r ℚ.* ℚ.1/ q)))) ⟩
    rational ℚ.∣ ((r ℚ.* ℚ.1/ r) ℚ.* ℚ.1/ q) ℚ.+ (ℚ.- q ℚ.* (ℚ.1/ r ℚ.* ℚ.1/ q)) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.+-cong (ℚ.≃-refl {(r ℚ.* ℚ.1/ r) ℚ.* ℚ.1/ q}) (ℚ.≃-sym (ℚ.*-assoc (ℚ.- q) (ℚ.1/ r) (ℚ.1/ q))))) ⟩
    rational ℚ.∣ ((r ℚ.* ℚ.1/ r) ℚ.* ℚ.1/ q) ℚ.+ ((ℚ.- q ℚ.* ℚ.1/ r) ℚ.* ℚ.1/ q) ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.*-distribʳ-+ (ℚ.1/ q) (r ℚ.* ℚ.1/ r) (ℚ.- q ℚ.* ℚ.1/ r)))) ⟩
    rational ℚ.∣ (r ℚ.* ℚ.1/ r ℚ.+ (ℚ.- q ℚ.* ℚ.1/ r)) ℚ.* ℚ.1/ q ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ.*-cong (ℚ.*-distribʳ-+ (ℚ.1/ r) r (ℚ.- q)) (ℚ.≃-refl {ℚ.1/ q})))) ⟩
    rational ℚ.∣ ((r ℚ.- q) ℚ.* ℚ.1/ r) ℚ.* ℚ.1/ q ∣
  ≈⟨ rational-cong (ℚ.∣-∣-cong (ℚ.*-assoc (r ℚ.- q) (ℚ.1/ r) (ℚ.1/ q))) ⟩
    rational ℚ.∣ (r ℚ.- q) ℚ.* (ℚ.1/ r ℚ.* ℚ.1/ q) ∣
  ≈⟨ rational-cong (ℚ.∣p*q∣≃∣p∣*∣q∣ (r ℚ.- q) (ℚ.1/ r ℚ.* ℚ.1/ q)) ⟩
    rational (ℚ.∣ r ℚ.- q ∣ ℚ.* ℚ.∣ ℚ.1/ r ℚ.* ℚ.1/ q ∣)
  ≈⟨ rational-cong (ℚ.*-comm ℚ.∣ r ℚ.- q ∣ ℚ.∣ ℚ.1/ r ℚ.* ℚ.1/ q ∣) ⟩
    rational (ℚ.∣ ℚ.1/ r ℚ.* ℚ.1/ q ∣ ℚ.* ℚ.∣ r ℚ.- q ∣)
  ≈⟨ ≃-sym (rational-* _ _ (ℚ.0≤∣p∣ (ℚ.1/ r ℚ.* ℚ.1/ q)) (ℚ.0≤∣p∣ (r ℚ.- q))) ⟩
    rational ℚ.∣ ℚ.1/ r ℚ.* ℚ.1/ q ∣ * rational ℚ.∣ r ℚ.- q ∣
  ≈⟨ ≃-refl ⟩
    rational ℚ.∣ ℚ.1/ (ℚ⁺.fog r⁺) ℚ.* ℚ.1/ (ℚ⁺.fog q⁺) ∣ * rational ℚ.∣ r ℚ.- q ∣
  ≈⟨ *-cong (rational-cong (ℚ.∣-∣-cong (ℚ.*-cong (ℚ⁺.1/-fog r⁺ r≢0) (ℚ⁺.1/-fog q⁺ q≢0)))) ≃-refl ⟩
    rational ℚ.∣ ℚ⁺.fog (ℚ⁺.1/ r⁺) ℚ.* ℚ⁺.fog (ℚ⁺.1/ q⁺) ∣ * rational ℚ.∣ r ℚ.- q ∣
  ≈⟨ *-cong (rational-cong (ℚ.∣-∣-cong (ℚ.≃-sym (ℚ⁺.*-fog (ℚ⁺.1/ r⁺) (ℚ⁺.1/ q⁺))))) ≃-refl ⟩
    rational ℚ.∣ ℚ⁺.fog (ℚ⁺.1/ r⁺ ℚ⁺.* ℚ⁺.1/ q⁺) ∣ * rational ℚ.∣ r ℚ.- q ∣
  ≈⟨ *-cong (rational-cong (ℚ⁺.∣-∣-fog (ℚ⁺.1/ r⁺ ℚ⁺.* ℚ⁺.1/ q⁺))) ≃-refl ⟩
    rational+ (ℚ⁺.1/ r⁺ ℚ⁺.* ℚ⁺.1/ q⁺) * rational ℚ.∣ r ℚ.- q ∣
  ≤⟨ *-mono-≤ (rational-mono (ℚ⁺.fog-mono (ℚ⁺.*-mono-≤ (ℚ⁺.1/-invert-≤ a r⁺ (ℚ⁺.r≤r a≤r))
                                                       (ℚ⁺.1/-invert-≤ a q⁺ (ℚ⁺.r≤r a≤q)))))
              ≤-refl ⟩
    rational+ (ℚ⁺.1/ a ℚ⁺.* ℚ⁺.1/ a) * rational ℚ.∣ r ℚ.- q ∣
  ≈⟨ *-cong (rational-cong (ℚ⁺.fog-cong (⁻¹-∙-comm a a))) (rational-cong (dist-sym r q)) ⟩
    rational+ (ℚ⁺.1/ (a ℚ⁺.* a)) * rational ℚ.∣ q ℚ.- r ∣
  ∎
  where open ≤-Reasoning
        open import Algebra.Properties.AbelianGroup ℚ⁺.*-AbelianGroup
        r≢0 = nonzero a r a≤r
        q≢0 = nonzero a q a≤q
        r⁺ = ℚ⁺.⟨ r , ℚ.positive (ℚ.<-≤-trans (ℚ.positive⁻¹ (a .ℚ⁺.positive)) a≤r) ⟩
        q⁺ = ℚ⁺.⟨ q , ℚ.positive (ℚ.<-≤-trans (ℚ.positive⁻¹ (a .ℚ⁺.positive)) a≤q) ⟩
