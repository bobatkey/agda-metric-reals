module metric2.rationals where

open import Algebra using (AbelianGroup)
open import Relation.Binary using (_Preserves₂_⟶_⟶_; IsDecTotalOrder)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product

-- Every totally ordered abelian group has an absolute value operator
module absolute {c ℓ}
    (A               : AbelianGroup c ℓ)
    (open AbelianGroup A renaming (Carrier to ∣A∣; _∙_ to _+_; ε to 0A; _⁻¹ to -_))
    (_≤_             : ∣A∣ → ∣A∣ → Set)
    (+-mono          : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_)
    (isDecTotalOrder : IsDecTotalOrder _≈_ _≤_)
  where
  open IsDecTotalOrder isDecTotalOrder
     using (total; isPartialOrder; antisym)
     renaming (refl to ≤-refl; trans to ≤-trans; reflexive to ≤-reflexive)
   open import Algebra.Properties.AbelianGroup (A)

  abs : ∣A∣ → ∣A∣
  abs x with total 0A x
  ... | inj₁ p = x
  ... | inj₂ p = - x

  abs-cong : ∀ {x y} → x ≈ y → abs x ≈ abs y
  abs-cong {x}{y} x≈y with total 0A x
  abs-cong {x}{y} x≈y | inj₁ 0≤x with total 0A y
  abs-cong {x}{y} x≈y | inj₁ 0≤x | inj₁ 0≤y = x≈y
  abs-cong {x}{y} x≈y | inj₁ 0≤x | inj₂ y≤0 = begin
                                                x     ≈⟨ antisym (≤-trans (≤-reflexive x≈y) y≤0) 0≤x ⟩
                                                0A    ≈⟨ sym ε⁻¹≈ε ⟩
                                                - 0A  ≈⟨ ⁻¹-cong (antisym (≤-trans 0≤x (≤-reflexive x≈y)) y≤0) ⟩
                                                - y
                                             ∎
    where open import Relation.Binary.Reasoning.Setoid setoid
  abs-cong {x}{y} x≈y | inj₂ x≤0 with total 0A y
  abs-cong {x}{y} x≈y | inj₂ x≤0 | inj₁ 0≤y = begin
                                                - x   ≈⟨ ⁻¹-cong (antisym x≤0 (≤-trans 0≤y (≤-reflexive (sym x≈y)))) ⟩
                                                - 0A  ≈⟨ ε⁻¹≈ε ⟩
                                                0A    ≈⟨ antisym 0≤y (≤-trans (≤-reflexive (sym x≈y)) x≤0) ⟩
                                                y
                                             ∎
    where open import Relation.Binary.Reasoning.Setoid setoid
  abs-cong {x}{y} x≈y | inj₂ x≤0 | inj₂ y≤0 = ⁻¹-cong x≈y

  private
    switch0 : ∀ {x y} → x ≤ y → (- y) ≤ (- x)
    switch0 {x}{y} x≤y =
       ≤-trans (≤-reflexive (sym (xyx⁻¹≈y x (- y))))
      (≤-trans (≤-reflexive (assoc _ _ _))
      (≤-trans (+-mono x≤y ≤-refl)
      (≤-trans (≤-reflexive (sym (assoc _ _ _)))
      (≤-trans (+-mono (≤-reflexive (inverse .proj₂ y)) ≤-refl)
               (≤-reflexive (identity .proj₁ (- x)))))))

    switch : ∀ {x y} → (- x) ≤ (- y) → y ≤ x
    switch {x}{y} -x≤-y = ≤-trans (≤-reflexive (sym (⁻¹-involutive y)))
                         (≤-trans (switch0 -x≤-y)
                                  (≤-reflexive (⁻¹-involutive x)))

    switch1 : ∀ {x} → x ≤ 0A → 0A ≤ (- x)
    switch1 {x} x≤0 = ≤-trans (≤-reflexive (sym ε⁻¹≈ε)) (switch0 x≤0)

    switch3 : ∀ {x} → (- x) ≤ 0A → 0A ≤ x
    switch3 {x} -x≤0 = switch (≤-trans -x≤0 (≤-reflexive (sym ε⁻¹≈ε)))

    switch2 : ∀ {x} → 0A ≤ x → (- x) ≤ 0A
    switch2 {x} 0≤x = ≤-trans (switch0 0≤x) (≤-reflexive ε⁻¹≈ε)

    blah : ∀ {x} → 0A ≤ x → 0A ≤ (- x) → - x ≈ 0A
    blah 0≤x 0≤-x = antisym (switch2 0≤x) 0≤-x

    bloo : ∀ {x} → 0A ≤ x → 0A ≤ (- x) → 0A ≈ x
    bloo {x} 0≤x 0≤-x = sym (trans (sym (⁻¹-involutive x)) (trans (⁻¹-cong (blah 0≤x 0≤-x)) ε⁻¹≈ε))

  non-negative : ∀ {x} → 0A ≤ abs x
  non-negative {x} with total 0A x
  non-negative {x} | inj₁ 0≤x = 0≤x
  non-negative {x} | inj₂ x≤0 = switch1 x≤0

  positive-definite : ∀ {x} → abs x ≈ 0A → x ≈ 0A
  positive-definite {x} ∣x∣≈0 with total 0A x
  positive-definite {x} ∣x∣≈0 | inj₁ 0≤x = ∣x∣≈0
  positive-definite {x} ∣x∣≈0 | inj₂ x≤0 = trans (trans (sym (⁻¹-involutive x)) (⁻¹-cong ∣x∣≈0)) ε⁻¹≈ε

  already-positive : ∀ x → 0A ≤ x → abs x ≈ x
  already-positive x 0≤x with total 0A x
  ... | inj₁ _ = refl
  ... | inj₂ x≤0 = trans (⁻¹-cong (antisym x≤0 0≤x)) (trans ε⁻¹≈ε (antisym 0≤x x≤0))

  pos-def₂ : ∀ {x} → x ≈ 0A → abs x ≈ 0A -- FIXME: just abs 0A ≈ 0A
  pos-def₂ {x} x≈0 with total 0A x
  ... | inj₁ 0≤x = x≈0
  ... | inj₂ x≤0 = trans (⁻¹-cong x≈0) ε⁻¹≈ε

  abs-inc : ∀ {x} → x ≤ abs x
  abs-inc {x} with total 0A x
  ... | inj₁ 0≤x = ≤-refl
  ... | inj₂ x≤0 = ≤-trans x≤0 (switch1 x≤0)

  abs-inc₂ : ∀ {x} → (- x) ≤ abs x
  abs-inc₂ {x} with total 0A x
  ... | inj₁ 0≤x = ≤-trans (switch2 0≤x) 0≤x
  ... | inj₂ x≤0 = ≤-refl

  sub-add : ∀ {x y} → abs (x + y) ≤ (abs x + abs y)
  sub-add {x}{y} with total 0A (x + y)
  sub-add {x}{y} | inj₁ 0≤x+y = +-mono abs-inc abs-inc
  sub-add {x}{y} | inj₂ x+y≤0 = ≤-trans (≤-reflexive (sym (⁻¹-∙-comm x y))) (+-mono abs-inc₂ abs-inc₂)

  -- must be an easier way than this...
  even : ∀ {x} → abs (- x) ≈ abs x
  even {x} with total 0A x
  even {x} | inj₁ 0≤x with total 0A (- x)
  even {x} | inj₁ 0≤x | inj₁ 0≤-x = trans (blah 0≤x 0≤-x) (bloo 0≤x 0≤-x)
  even {x} | inj₁ 0≤x | inj₂ -x≤0 = ⁻¹-involutive x
  even {x} | inj₂ x≤0 with total 0A (- x)
  even {x} | inj₂ x≤0 | inj₁ 0≤-x = refl
  even {x} | inj₂ x≤0 | inj₂ -x≤0 =
     trans (blah (switch3 (≤-trans (≤-reflexive (⁻¹-involutive x)) x≤0))
                 (≤-trans (≤-reflexive (sym ε⁻¹≈ε)) (switch0 -x≤0)))
           (bloo (switch3 (≤-trans (≤-reflexive (⁻¹-involutive x)) x≤0))
                 (switch (≤-trans (≤-reflexive (⁻¹-involutive (- x))) (≤-trans -x≤0 (≤-reflexive (sym ε⁻¹≈ε))))))
{-
  -- every abelian group is a module over the integers...
  open import Data.Integer using (ℤ; ∣_∣; +_; -[1+_])
  open import Data.Nat using (ℕ; zero; suc)

  sum : ℕ → ∣A∣ → ∣A∣
  sum zero a = 0A
  sum (suc n) a = a + sum n a

  sum-nonneg : ∀ n a → 0A ≤ a → 0A ≤ sum n a
  sum-nonneg zero a 0≤a = ≤-refl
  sum-nonneg (suc n) a 0≤a = ≤-trans (≤-reflexive (sym (identityʳ 0A))) (+-mono 0≤a (sum-nonneg n a 0≤a))

  _·_ : ℤ → ∣A∣ → ∣A∣
  (+ n) · a = sum n a
  (-[1+ n ]) · a = - (sum (suc n) a)

  multiplicative : ∀ z a → abs (z · a) ≈ ((+ ∣ z ∣) · abs a)
  multiplicative (+ n)    a with total 0A a
  ... | inj₁ 0≤a = already-positive (sum n a) (sum-nonneg n a 0≤a)
  ... | inj₂ a≤0 = {!!}
  multiplicative -[1+ n ] a = {!!}
-}

open import Data.Rational.Unnormalised as ℚ using () renaming (ℚᵘ to ℚ; 0ℚᵘ to 0ℚ; 1ℚᵘ to 1ℚ)
import Data.Rational.Unnormalised.Properties as ℚ
open import metric2.base
open import upper-reals

open absolute ℚ.+-0-abelianGroup ℚ._≤_ ℚ.+-mono-≤ ℚ.≤-isDecTotalOrder

open MSpc
open _⇒_

-- FIXME: this ought to work for any abelian group with a norm : G → ℝᵘ
ℚspc : MSpc
ℚspc .Carrier = ℚ
ℚspc .dist x y = rational (abs (x ℚ.- y))
ℚspc .refl {x} = ≤-trans (rational-mono (ℚ.≤-reflexive (pos-def₂ (ℚ.+-inverseʳ x)))) rational-0
ℚspc .sym {x}{y} = rational-mono (ℚ.≤-reflexive (ℚ.≃-trans (abs-cong eq) (even {y ℚ.- x})))
  where open import Algebra.Properties.AbelianGroup ℚ.+-0-abelianGroup
        -- FIXME: tidy this up
        eq : x ℚ.- y ℚ.≃ ℚ.- (y ℚ.- x)
        eq = ℚ.≃-trans (ℚ.+-comm x (ℚ.- y))
            (ℚ.≃-trans (ℚ.+-congʳ (ℚ.- y) (ℚ.≃-sym (⁻¹-involutive x)))
                       (⁻¹-∙-comm y (ℚ.- x)))
ℚspc .triangle {x}{y}{z} =
  ≤-trans (rational-mono (ℚ.≤-trans (ℚ.≤-reflexive (abs-cong {x ℚ.- z}{(x ℚ.- y) ℚ.+ (y ℚ.- z)} {!!})) (sub-add {x ℚ.- y} {y ℚ.- z}))) {!!}

open import metric2.monoidal
open import metric2.terminal

const : ℚ → ⊤ₘ ⇒ ℚspc
const q .fun _ = q
const q .non-expansive = ℚspc .refl {q}

add : (ℚspc ⊗ ℚspc) ⇒ ℚspc
add .fun (a , b) = a ℚ.+ b
add .non-expansive = {!!}

negate : ℚspc ⇒ ℚspc
negate .fun a = ℚ.- a
negate .non-expansive {a}{b} =
  rational-mono (ℚ.≤-reflexive (abs-cong {ℚ.- a ℚ.- ℚ.- b} {a ℚ.- b} {!!}))

-- this gives a quantitative abelian group
--    x :2 ℚspc |- x + (- x) ≡ 0   (assuming weakening)
--    + associativity and commutativity

open import metric2.scaling
open import qpos as ℚ⁺ using (ℚ⁺)

-- FIXME: make this work for any q : ℚ
ℚ-scale : (q : ℚ⁺) → ![ q ] ℚspc ⇒ ℚspc
ℚ-scale q .fun a = ℚ⁺.fog q ℚ.* a
ℚ-scale q .non-expansive = {!!}

{-
mul : ∀ a → (ℚspc[ - a , a ] ⊗ ![ abs a ] ℚspc) ⇒ ℚspc -- FIXME: output bound?
mul = ?

recip : ∀ a → ![ a ] ℚspc[ a ⟩ ⇒ ℚspc
recip = ?
-}

------------------------------------------------------------------------------
-- the real numbers as the completion of the rationals
{-
open import metric2.completion renaming (map to 𝒞-map)
open metric2.base.category

ℝspc : MSpc
ℝspc = 𝒞 ℚspc

ℝ : Set
ℝ = ℝspc .Carrier

addℝ : (ℝspc ⊗ ℝspc) ⇒ ℝspc
addℝ = 𝒞-map add ∘ {!monoidal-⊗!}
-}
