{-# OPTIONS --without-K --safe #-}

module metric2.base where

open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence; Setoid)
open import upper-reals hiding (isEquivalence)

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

module category where

  open MSpc
  open _⇒_
  open _≈f_

  id : ∀ {X} → X ⇒ X
  id .fun x = x
  id .non-expansive = ≤-refl

  infixr 9 _∘_

  _∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
  (f ∘ g) .fun x = f .fun (g .fun x)
  (f ∘ g) .non-expansive = ≤-trans (f .non-expansive) (g .non-expansive)

  ∘-cong : ∀ {X Y Z}{f₁ f₂ : Y ⇒ Z}{g₁ g₂ : X ⇒ Y} →
          f₁ ≈f f₂ → g₁ ≈f g₂ →
          (f₁ ∘ g₁) ≈f (f₂ ∘ g₂)
  ∘-cong {X}{Y}{Z}{f₁}{f₂}{g₁}{g₂} f₁≈f₂ g₁≈g₂ .f≈f a =
    Z .≈-trans (f₁≈f₂ .f≈f (g₁ .fun a)) (cong f₂ (g₁≈g₂ .f≈f a))

  identityˡ : ∀ {X Y}(f : X ⇒ Y) → (f ∘ id) ≈f f
  identityˡ {X}{Y} f .f≈f a = Y .refl

  identityʳ : ∀ {X Y}(f : X ⇒ Y) → (id ∘ f) ≈f f
  identityʳ {X}{Y} f .f≈f a = Y .refl

  assoc : ∀ {W X Y Z}(f : Y ⇒ Z)(g : X ⇒ Y)(h : W ⇒ X) →
          (f ∘ g ∘ h) ≈f ((f ∘ g) ∘ h)
  assoc {Z = Z} f g h .f≈f w = Z .refl
