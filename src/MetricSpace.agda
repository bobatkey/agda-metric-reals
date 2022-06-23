{-# OPTIONS --without-K --safe #-}

module MetricSpace where

open import Level using (0ℓ)
open import Data.Product using (_,_)
open import Relation.Binary using (IsEquivalence; Setoid)
open import Data.Real.UpperClosed

record MSpc : Set₁ where
  no-eta-equality
  field
    Carrier  : Set
    dist     : Carrier → Carrier → ℝᵘ
    refl     : ∀ {x} → dist x x ≤ 0ℝ
    sym      : ∀ {x y} → dist x y ≤ dist y x
    triangle : ∀ {x y z} → dist x z ≤ (dist x y + dist y z)

  _≈_ : Carrier → Carrier → Set
  x ≈ y = dist x y ≤ 0ℝ

  isEquivalence : IsEquivalence _≈_
  isEquivalence =
     record { refl  = refl
            ; sym   = ≤-trans sym
            ; trans = λ {x}{y}{z} x-y y-z →
                         begin
                           dist x z
                         ≤⟨ triangle ⟩
                           dist x y + dist y z
                         ≤⟨ +-mono-≤ x-y y-z ⟩
                           0ℝ + 0ℝ
                         ≈⟨ +-identityʳ 0ℝ ⟩
                           0ℝ
                         ∎
            }
    where open ≤-Reasoning

  open IsEquivalence isEquivalence renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans) public

  setoid : Setoid 0ℓ 0ℓ
  setoid = record { isEquivalence = isEquivalence }

  sym-eq : ∀ {x y} → dist x y ≃ dist y x
  sym-eq = sym , sym

  refl-0 : ∀ {x} → dist x x ≃ 0ℝ
  refl-0 = refl , 0-least _

-- non-expansive functions
record _⇒_ (X Y : MSpc) : Set where
  no-eta-equality
  private
    module X = MSpc X
    module Y = MSpc Y
  field
    fun           : X.Carrier → Y.Carrier
    non-expansive : ∀ {a b} → Y.dist (fun a) (fun b) ≤ X.dist a b
  cong : ∀ {x₁ x₂} → x₁ X.≈ x₂ → fun x₁ Y.≈ fun x₂
  cong x₁≈x₂ = ≤-trans non-expansive x₁≈x₂

record _≈f_ {X Y} (f g : X ⇒ Y) : Set where
  open MSpc Y using (_≈_)
  open _⇒_
  field
    f≈f : ∀ a → f .fun a ≈ g .fun a

≈f-isEquivalence : ∀ {X Y} → IsEquivalence (_≈f_ {X} {Y})
≈f-isEquivalence {X}{Y} =
  record { refl = record { f≈f = λ a → Y .≈-refl }
         ; sym = λ f≈g → record { f≈f = λ a → Y .≈-sym (f≈g .f≈f a) }
         ; trans = λ f≈g g≈h → record { f≈f = λ a → Y .≈-trans (f≈g .f≈f a) (g≈h .f≈f a) }
         }
  where open _⇒_; open _≈f_; open MSpc

≈f-setoid : ∀ {X Y} → Setoid 0ℓ 0ℓ
≈f-setoid {X}{Y} = record { Carrier = X ⇒ Y ; isEquivalence = ≈f-isEquivalence }
