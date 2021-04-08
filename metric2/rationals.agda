{-# OPTIONS --without-K --safe #-}

module metric2.rationals where

open import Algebra using (AbelianGroup)
open import Relation.Binary using (_Preserves₂_⟶_⟶_; IsDecTotalOrder)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂; _,_)

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

  non-negative : ∀ x → 0A ≤ abs x
  non-negative x with total 0A x
  non-negative x | inj₁ 0≤x = 0≤x
  non-negative x | inj₂ x≤0 = switch1 x≤0

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

  sub-add : ∀ x y → abs (x + y) ≤ (abs x + abs y)
  sub-add x y with total 0A (x + y)
  sub-add x y | inj₁ 0≤x+y = +-mono abs-inc abs-inc
  sub-add x y | inj₂ x+y≤0 = ≤-trans (≤-reflexive (sym (⁻¹-∙-comm x y))) (+-mono abs-inc₂ abs-inc₂)

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

open absolute ℚ.+-0-abelianGroup ℚ._≤_ ℚ.+-mono-≤ ℚ.≤-isDecTotalOrder public

open MSpc
open _⇒_
open _≈f_

ℚspc : MSpc
ℚspc .Carrier = ℚ
ℚspc .dist x y = rational (abs (x ℚ.- y))
ℚspc .refl {x} =
  begin
    rational (abs (x ℚ.- x))
  ≈⟨ rational-cong (pos-def₂ (ℚ.+-inverseʳ x)) ⟩
    rational 0ℚ
  ≈⟨ rational-0 ⟩
    0ℝ
  ∎
  where open ≤-Reasoning
ℚspc .sym {x}{y} = rational-mono (ℚ.≤-reflexive (ℚ.≃-trans (abs-cong eq) (even {y ℚ.- x})))
  where open import Algebra.Properties.AbelianGroup ℚ.+-0-abelianGroup
        -- FIXME: tidy this up
        eq : x ℚ.- y ℚ.≃ ℚ.- (y ℚ.- x)
        eq = ℚ.≃-trans (ℚ.+-comm x (ℚ.- y))
            (ℚ.≃-trans (ℚ.+-congʳ (ℚ.- y) (ℚ.≃-sym (⁻¹-involutive x)))
                       (⁻¹-∙-comm y (ℚ.- x)))
ℚspc .triangle {x}{y}{z} =
  -- FIXME: tidy this up
  ≤-trans (rational-mono (ℚ.≤-trans (ℚ.≤-reflexive (abs-cong {x ℚ.- z}{(x ℚ.- y) ℚ.+ (y ℚ.- z)} p)) (sub-add (x ℚ.- y) (y ℚ.- z))))
    (≤-reflexive (≃-sym (rational-+ (abs (x ℚ.- y)) (abs (y ℚ.- z)) (non-negative (x ℚ.- y)) (non-negative (y ℚ.- z)))))
  where open ℚ.≤-Reasoning
        p : x ℚ.- z ℚ.≃ x ℚ.- y ℚ.+ (y ℚ.- z)
        p = begin-equality
              x ℚ.- z
            ≈⟨ ℚ.+-congʳ x (ℚ.≃-sym (ℚ.+-identityˡ (ℚ.- z))) ⟩
              x ℚ.+ (0ℚ ℚ.- z)
            ≈⟨ ℚ.+-congʳ x (ℚ.+-congˡ (ℚ.- z) (ℚ.≃-sym (ℚ.+-inverseˡ y))) ⟩
              x ℚ.+ ((ℚ.- y ℚ.+ y) ℚ.- z)
            ≈⟨ ℚ.+-congʳ x (ℚ.+-assoc (ℚ.- y) y (ℚ.- z)) ⟩
              x ℚ.+ (ℚ.- y ℚ.+ (y ℚ.- z))
            ≈⟨ ℚ.≃-sym (ℚ.+-assoc x (ℚ.- y) (y ℚ.- z)) ⟩
              x ℚ.- y ℚ.+ (y ℚ.- z)
            ∎

ℚspc-≈ : ∀ {q r} → q ℚ.≃ r → _≈_ ℚspc q r
ℚspc-≈ {q}{r} q≃r =
  begin
    rational (abs (q ℚ.- r))
  ≈⟨ rational-cong (abs-cong (ℚ.+-congˡ (ℚ.- r) q≃r)) ⟩
    rational (abs (r ℚ.- r))
  ≈⟨ rational-cong (abs-cong (ℚ.+-inverseʳ r)) ⟩
    rational (abs 0ℚ)
  ≈⟨ rational-cong (pos-def₂ ℚ.≃-refl) ⟩
    rational 0ℚ
  ≈⟨ rational-0 ⟩
    0ℝ
  ∎
  where open ≤-Reasoning


open import metric2.monoidal
open import metric2.terminal
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
    rational (abs (a₁ ℚ.+ b₁ ℚ.- (a₂ ℚ.+ b₂)))
  ≈⟨ rational-cong (abs-cong (ℚ.+-congʳ (a₁ ℚ.+ b₁) (ℚ.≃-sym (⁻¹-∙-comm a₂ b₂)))) ⟩
    rational (abs (a₁ ℚ.+ b₁ ℚ.+ (ℚ.- a₂ ℚ.- b₂)))
  ≈⟨ rational-cong (abs-cong (ℚ-interchange a₁ b₁ (ℚ.- a₂) (ℚ.- b₂))) ⟩
    rational (abs ((a₁ ℚ.- a₂) ℚ.+ (b₁ ℚ.- b₂)))
  ≤⟨ rational-mono (sub-add (a₁ ℚ.- a₂) (b₁ ℚ.- b₂)) ⟩
    rational (abs (a₁ ℚ.- a₂) ℚ.+ abs (b₁ ℚ.- b₂))
  ≈⟨ ≃-sym (rational-+ (abs (a₁ ℚ.- a₂)) (abs (b₁ ℚ.- b₂)) (non-negative (a₁ ℚ.- a₂)) (non-negative (b₁ ℚ.- b₂))) ⟩
    dist (ℚspc ⊗ ℚspc) (a₁ , b₁) (a₂ , b₂)
  ∎
  where open ≤-Reasoning
        open import Algebra.Properties.AbelianGroup (ℚ.+-0-abelianGroup)

add-identityˡ : (add ∘ (zero ⊗f id) ∘ left-unit⁻¹) ≈f id
add-identityˡ .f≈f a = ℚspc-≈ (ℚ.+-identityˡ a)

add-comm : (add ∘ swap) ≈f add
add-comm .f≈f (a , b) = ℚspc-≈ (ℚ.+-comm b a)

add-assoc : (add ∘ (add ⊗f id) ∘ ⊗-assoc) ≈f (add ∘ (id ⊗f add))
add-assoc .f≈f (a , (b , c)) = ℚspc-≈ (ℚ.+-assoc a b c)

------------------------------------------------------------------------------
-- Negation, so we have a (graded) abelian group object

negate : ℚspc ⇒ ℚspc
negate .fun a = ℚ.- a
negate .non-expansive {a}{b} =
  begin
    rational (abs (ℚ.- a ℚ.- ℚ.- b))
  ≈⟨ rational-cong (abs-cong (⁻¹-∙-comm a (ℚ.- b))) ⟩
    rational (abs (ℚ.- (a ℚ.- b)))
  ≈⟨ rational-cong (even {a ℚ.- b}) ⟩
    dist ℚspc a b
  ∎
  where open ≤-Reasoning
        open import Algebra.Properties.AbelianGroup (ℚ.+-0-abelianGroup)

-- this gives a quantitative abelian group
--    x :2 ℚspc |- x + (- x) ≡ 0   (assuming weakening)

------------------------------------------------------------------------------
-- Multiplication by a "scalar"
open import metric2.scaling
{-
-- FIXME: make this work for any q : ℚ; need scaling to work for non-negative rationals
ℚ-scale : (q : ℚ⁺) → ![ q ] ℚspc ⇒ ℚspc
ℚ-scale q .fun a = ℚ⁺.fog q ℚ.* a
ℚ-scale q .non-expansive {a}{b} =
  begin
    rational (abs (ℚ⁺.fog q ℚ.* a ℚ.- ℚ⁺.fog q ℚ.* b))
  ≈⟨ rational-cong (abs-cong (ℚ.+-congʳ (ℚ⁺.fog q ℚ.* a) (ℚ.neg-distribʳ-* (ℚ⁺.fog q) b))) ⟩
    rational (abs (ℚ⁺.fog q ℚ.* a ℚ.+ ℚ⁺.fog q ℚ.* (ℚ.- b)))
  ≈⟨ rational-cong (abs-cong (ℚ.≃-sym (ℚ.*-distribˡ-+ (ℚ⁺.fog q) a (ℚ.- b)))) ⟩
    rational (abs (ℚ⁺.fog q ℚ.* (a ℚ.- b)))
  ≈⟨ rational-cong {!!} ⟩
    rational (ℚ⁺.fog q ℚ.* abs (a ℚ.- b))
  ≈⟨ {!!} ⟩ -- rational-scale q (abs (a ℚ.- b)) (non-negative (a ℚ.- b)) ⟩
    rational+ q * rational (abs (a ℚ.- b))
  ≈⟨ ≃-refl ⟩
    rational+ q * ℚspc .dist a b
  ≈⟨ ≃-refl ⟩
    dist (![ q ] ℚspc) a b
  ∎
  where open ≤-Reasoning
-}
------------------------------------------------------------------------------
-- Multiplication

{-
-- FIXME: the following need sub-ranges of ℚspc to be defined

mul : ∀ a → (ℚspc[ - a , a ] ⊗ ![ abs a ] ℚspc) ⇒ ℚspc
mul = ?

recip : ∀ a → ![ a ] ℚspc[ a ⟩ ⇒ ℚspc
recip = ?
-}
