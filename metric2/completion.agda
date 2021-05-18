{-# OPTIONS --without-K --safe #-}

module metric2.completion where

open import Data.Product using (_×_; _,_; proj₁; proj₂; swap)
import qpos as ℚ⁺
open ℚ⁺ using (ℚ⁺; _/2; 1/_; 1ℚ⁺)
open import metric2.base
open import upper-reals

open MSpc
open _⇒_
open _≈f_

record RegFun (X : MSpc) : Set where
  field
    rfun    : ℚ⁺ → X .Carrier
    regular : ∀ ε₁ ε₂ → X .dist (rfun ε₁) (rfun ε₂) ≤ rational+ (ε₁ ℚ⁺.+ ε₂)
open RegFun

reg-dist : ∀ {X} → RegFun X → RegFun X → ℝᵘ
reg-dist {X} x y = sup (ℚ⁺ × ℚ⁺) (λ { (ε₁ , ε₂) → X .dist (x .rfun ε₁) (y .rfun ε₂) ⊖ (ε₁ ℚ⁺.+ ε₂) } )

-- FIXME: some lemmas for dealing with reg-dist, to avoid all the
-- deadling with sup-least and ⊖-iso1/2 below

𝒞 : MSpc → MSpc
𝒞 X .Carrier = RegFun X
𝒞 X .dist = reg-dist
𝒞 X .refl {x} = sup-least λ { (ε₁ , ε₂) → ≤-trans (⊖-mono (x .regular ε₁ ε₂) ℚ⁺.≤-refl) (⊖-0 (ε₁ ℚ⁺.+ ε₂)) }
𝒞 X .sym = sup-mono-≤ swap λ { (ε₁ , ε₂) → ⊖-mono (X .sym) (ℚ⁺.≤-reflexive (ℚ⁺.+-comm ε₂ ε₁)) }
𝒞 X .triangle {x}{y}{z} =
  sup-least λ { (ε₁ , ε₂) → closedness λ ε →
                  begin
                     (X .dist (x .rfun ε₁) (z .rfun ε₂) ⊖ (ε₁ ℚ⁺.+ ε₂)) ⊖ ε
                       ≤⟨ ⊖-mono (⊖-mono (X .triangle) ℚ⁺.≤-refl) (ℚ⁺.≤-reflexive ℚ⁺.half+half) ⟩
                     ((X .dist (x .rfun ε₁) (y .rfun (ε /2)) + X .dist (y .rfun (ε /2)) (z .rfun ε₂)) ⊖ (ε₁ ℚ⁺.+ ε₂)) ⊖ (ε /2 ℚ⁺.+ ε /2)
                       ≈⟨ ⊖-+ ⟩
                     ((X .dist (x .rfun ε₁) (y .rfun (ε /2)) + X .dist (y .rfun (ε /2)) (z .rfun ε₂)) ⊖ ((ε₁ ℚ⁺.+ ε₂) ℚ⁺.+ (ε /2 ℚ⁺.+ ε /2)))
                       ≤⟨ ⊖-mono ≤-refl (ℚ⁺.≤-reflexive (ℚ⁺-interchange ε₁ _ _ _)) ⟩
                     ((X .dist (x .rfun ε₁) (y .rfun (ε /2)) + X .dist (y .rfun (ε /2)) (z .rfun ε₂)) ⊖ ((ε₁ ℚ⁺.+ ε /2) ℚ⁺.+ (ε₂ ℚ⁺.+ ε /2)))
                       ≤⟨ ⊖-mono ≤-refl (ℚ⁺.≤-reflexive (ℚ⁺.+-congʳ (ε₁ ℚ⁺.+ ε /2) (ℚ⁺.+-comm _ _))) ⟩
                     ((X .dist (x .rfun ε₁) (y .rfun (ε /2)) + X .dist (y .rfun (ε /2)) (z .rfun ε₂)) ⊖ ((ε₁ ℚ⁺.+ ε /2) ℚ⁺.+ (ε /2 ℚ⁺.+ ε₂)))
                       ≤⟨ ⊖-+-+ ⟩
                     (X .dist (x .rfun ε₁) (y .rfun (ε /2)) ⊖ (ε₁ ℚ⁺.+ ε /2)) + (X .dist (y .rfun (ε /2)) (z .rfun ε₂) ⊖ (ε /2 ℚ⁺.+ ε₂))
                       ≤⟨ +-mono-≤ (sup-upper (ε₁ , ε /2)) (sup-upper (ε /2 , ε₂)) ⟩
                     reg-dist x y + reg-dist y z
                   ∎
              }
   where open ≤-Reasoning

𝒞-≈ : ∀ {X} {x y : 𝒞 X .Carrier} →
       (∀ ε₁ ε₂ → X .dist (x .rfun ε₁) (y .rfun ε₂) ≤ rational+ (ε₁ ℚ⁺.+ ε₂)) →
       _≈_ (𝒞 X) x y
𝒞-≈ {X}{x}{y} h = sup-least λ { (ε₁ , ε₂) → ⊖-iso2
  (begin
    X .dist (x .rfun ε₁) (y .rfun ε₂)
  ≤⟨ h ε₁ ε₂ ⟩
    rational+ (ε₁ ℚ⁺.+ ε₂)
  ≈⟨ ≃-sym (+-identityˡ (rational+ (ε₁ ℚ⁺.+ ε₂))) ⟩
    0ℝ + rational+ (ε₁ ℚ⁺.+ ε₂)
  ∎) }
  where open ≤-Reasoning

------------------------------------------------------------------------------
-- Functor operation on morphisms

-- FIXME: does this also work for uniformly continuous functions?
map : ∀ {X Y} → X ⇒ Y → 𝒞 X ⇒ 𝒞 Y
map f .fun x .rfun ε = f .fun (x .rfun ε)
map f .fun x .regular ε₁ ε₂ = ≤-trans (f .non-expansive) (x .regular ε₁ ε₂)
map f .non-expansive = sup-mono-≤ (λ x → x) λ { (ε₁ , ε₂) → ⊖-mono (f .non-expansive) ℚ⁺.≤-refl }

map-cong : ∀ {X Y}{f₁ f₂ : X ⇒ Y} → f₁ ≈f f₂ → map f₁ ≈f map f₂
map-cong {X}{Y}{f₁}{f₂} f₁≈f₂ .f≈f x =
  𝒞-≈ {Y} {map f₁ .fun x} {map f₂ .fun x} λ ε₁ ε₂ →
  begin
    Y .dist (f₁ .fun (x .rfun ε₁)) (f₂ .fun (x .rfun ε₂))
  ≤⟨ Y .triangle ⟩
    Y .dist (f₁ .fun (x .rfun ε₁)) (f₁ .fun (x .rfun ε₂)) + Y .dist (f₁ .fun (x .rfun ε₂)) (f₂ .fun (x .rfun ε₂))
  ≤⟨ +-mono-≤ (f₁ .non-expansive) (f₁≈f₂ .f≈f (x .rfun ε₂)) ⟩
    X .dist (x .rfun ε₁) (x .rfun ε₂) + 0ℝ
  ≤⟨ +-mono-≤ (x .regular ε₁ ε₂) ≤-refl ⟩
    rational+ (ε₁ ℚ⁺.+ ε₂) + 0ℝ
  ≈⟨ +-identityʳ (rational+ (ε₁ ℚ⁺.+ ε₂)) ⟩
    rational+ (ε₁ ℚ⁺.+ ε₂)
  ∎
  where open ≤-Reasoning

open metric2.base.category

map-id : ∀ {X} → map {X} id ≈f id
map-id {X} .f≈f x = 𝒞 X .refl {x}

map-∘ : ∀ {X Y Z} {f : Y ⇒ Z} {g : X ⇒ Y} →
       map (f ∘ g) ≈f (map f ∘ map g)
map-∘ {Z = Z}{f}{g} .f≈f a = 𝒞 Z .refl {map f .fun (map g .fun a)}

------------------------------------------------------------------------------
unit : ∀ {X} → X ⇒ 𝒞 X
unit {X} .fun x .rfun _ = x
unit {X} .fun x .regular ε₁ ε₂ = ≤-trans (X .refl) (0-least _)
unit {X} .non-expansive {x}{y} =
   sup-least λ { (ε₁ , ε₂) →
                   begin
                      X .dist x y ⊖ (ε₁ ℚ⁺.+ ε₂)
                        ≤⟨ ⊖-≤ ⟩
                      X .dist x y
                   ∎ }
  where open ≤-Reasoning

unit-natural : ∀ {X Y}{f : X ⇒ Y} →
               (unit ∘ f) ≈f (map f ∘ unit)
unit-natural {X}{Y}{f} .f≈f x = (𝒞 Y) .refl {unit .fun (f .fun x)}

------------------------------------------------------------------------------
join : ∀ {X} → 𝒞 (𝒞 X) ⇒ 𝒞 X
join {X} .fun x .rfun ε = x .rfun (ε /2) .rfun (ε /2)
join {X} .fun x .regular ε₁ ε₂ =
   begin
     X .dist (x .rfun (ε₁ /2) .rfun (ε₁ /2)) (x .rfun (ε₂ /2) .rfun (ε₂ /2))
       ≤⟨ ⊖-iso1 (≤-trans (sup-upper (ε₁ /2 , ε₂ /2)) (x .regular (ε₁ /2) (ε₂ /2))) ⟩
     rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)
       ≈⟨ rational⁺-+ (ε₁ /2 ℚ⁺.+ ε₂ /2) (ε₁ /2 ℚ⁺.+ ε₂ /2) ⟩
     rational+ ((ε₁ /2 ℚ⁺.+ ε₂ /2) ℚ⁺.+ (ε₁ /2 ℚ⁺.+ ε₂ /2))
       ≤⟨ rational-mono (ℚ⁺.fog-mono (ℚ⁺.≤-reflexive (ℚ⁺-interchange (ε₁ /2) (ε₂ /2) (ε₁ /2) (ε₂ /2)))) ⟩
     rational+ ((ε₁ /2 ℚ⁺.+ ε₁ /2) ℚ⁺.+ (ε₂ /2 ℚ⁺.+ ε₂ /2))
       ≤⟨ rational-mono (ℚ⁺.fog-mono (ℚ⁺.≤-reflexive (ℚ⁺.+-cong (ℚ⁺.half+half {ε₁}) (ℚ⁺.half+half {ε₂})))) ⟩
     rational+ (ε₁ ℚ⁺.+ ε₂)
   ∎
   where open ≤-Reasoning
join {X} .non-expansive {a}{b} =
  sup-least (λ { (ε₁ , ε₂) → ⊖-iso2
    (begin
      X .dist (a .rfun (ε₁ /2) .rfun (ε₁ /2)) (b .rfun (ε₂ /2) .rfun (ε₂ /2))
    ≤⟨ ⊖-eval ⟩
      (X .dist (a .rfun (ε₁ /2) .rfun (ε₁ /2)) (b .rfun (ε₂ /2) .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)
    ≤⟨ +-mono-≤ (⊖-mono ⊖-eval ℚ⁺.≤-refl) ≤-refl ⟩
      (((X .dist (a .rfun (ε₁ /2) .rfun (ε₁ /2)) (b .rfun (ε₂ /2) .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)
    ≤⟨ +-mono-≤ (⊖-+-out _ (rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)) (ε₁ /2 ℚ⁺.+ ε₂ /2)) ≤-refl ⟩
      (((X .dist (a .rfun (ε₁ /2) .rfun (ε₁ /2)) (b .rfun (ε₂ /2) .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)
    ≈⟨ +-assoc _ (rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)) (rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)) ⟩
      ((X .dist (a .rfun (ε₁ /2) .rfun (ε₁ /2)) (b .rfun (ε₂ /2) .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) + (rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2))
    ≤⟨ +-mono-≤ (⊖-mono (sup-upper (ε₁ /2 , ε₂ /2)) ℚ⁺.≤-refl) (≤-reflexive (rational⁺-+ (ε₁ /2 ℚ⁺.+ ε₂ /2) (ε₁ /2 ℚ⁺.+ ε₂ /2))) ⟩
      (𝒞 X .dist (a .rfun (ε₁ /2)) (b .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) + rational+ ((ε₁ /2 ℚ⁺.+ ε₂ /2) ℚ⁺.+ (ε₁ /2 ℚ⁺.+ ε₂ /2))
    ≈⟨ +-cong ≃-refl (rational-cong (ℚ⁺.fog-cong (ℚ⁺-interchange (ε₁ /2) (ε₂ /2) (ε₁ /2) (ε₂ /2)))) ⟩
      (𝒞 X .dist (a .rfun (ε₁ /2)) (b .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) + rational+ ((ε₁ /2 ℚ⁺.+ ε₁ /2) ℚ⁺.+ (ε₂ /2 ℚ⁺.+ ε₂ /2))
    ≈⟨ +-cong ≃-refl (rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-cong (ℚ⁺.half+half {ε₁}) (ℚ⁺.half+half {ε₂})))) ⟩
      ((𝒞 X .dist (a .rfun (ε₁ /2)) (b .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) + rational+ (ε₁ ℚ⁺.+ ε₂))
    ≤⟨ +-mono-≤ (sup-upper (ε₁ /2 , ε₂ /2)) ≤-refl ⟩
      dist (𝒞 (𝒞 X)) a b + rational+ (ε₁ ℚ⁺.+ ε₂)
    ∎) })
  where open ≤-Reasoning

join-natural : ∀ {X Y}{f : X ⇒ Y} →
               (join ∘ map (map f)) ≈f (map f ∘ join)
join-natural {X}{Y}{f} .f≈f x = 𝒞 Y .refl {map f .fun (join .fun x)}

join-unit : ∀ {X} → (join ∘ unit) ≈f id {𝒞 X}
join-unit .f≈f a =
  sup-least (λ { (ε₁ , ε₂) →
   ≤-trans (⊖-mono (a .regular (ε₁ /2) ε₂) ℚ⁺.≤-refl)
           (⊖-iso2 (≤-trans (rational-mono (ℚ⁺.fog-mono (ℚ⁺.+-mono-≤ (ℚ⁺.half-≤ ε₁) (ℚ⁺.≤-refl {ε₂}))))
                            (≤-reflexive (≃-sym (+-identityˡ (rational+ (ε₁ ℚ⁺.+ ε₂))))))) })

join-mapunit : ∀ {X} → (join ∘ map unit) ≈f id {𝒞 X}
join-mapunit .f≈f a = join-unit .f≈f a

join-join : ∀ {X} → (join ∘ map join) ≈f (join ∘ join {𝒞 X})
join-join {X} .f≈f x =
  𝒞-≈ {X} {join .fun (map join .fun x)} {join .fun (join .fun x)} λ ε₁ ε₂ →
  ≤-trans (⊖-iso1 (≤-trans (sup-upper (ε₁ /2 /2 , ε₂ /2)) (⊖-iso1 (≤-trans (sup-upper (ε₁ /2 /2 , ε₂ /2 /2)) (x .regular (ε₁ /2) (ε₂ /2 /2)))))) (eq ε₁ ε₂)
  where
    open ≤-Reasoning
    open import CommutativeSemigroupSolver (ℚ⁺.+-commutativeSemigroup)
    a = v# 0; b = v# 1; c = v# 2; d = v# 3
    eq : ∀ ε₁ ε₂ → ((rational+ (ε₁ /2 ℚ⁺.+ (ε₂ /2) /2) + rational+ ((ε₁ /2) /2 ℚ⁺.+ (ε₂ /2) /2)) + rational+ ((ε₁ /2) /2 ℚ⁺.+ ε₂ /2)) ≤ rational+ (ε₁ ℚ⁺.+ ε₂)
    eq ε₁ ε₂ =
      begin
        (rational+ (ε₁ /2 ℚ⁺.+ (ε₂ /2) /2) + rational+ ((ε₁ /2) /2 ℚ⁺.+ (ε₂ /2) /2)) + rational+ ((ε₁ /2) /2 ℚ⁺.+ ε₂ /2)
           ≈⟨ +-cong (rational⁺-+ (ε₁ /2 ℚ⁺.+ (ε₂ /2) /2) ((ε₁ /2) /2 ℚ⁺.+ (ε₂ /2) /2)) ≃-refl ⟩
        rational+ ((ε₁ /2 ℚ⁺.+ (ε₂ /2) /2) ℚ⁺.+ ((ε₁ /2) /2 ℚ⁺.+ (ε₂ /2) /2)) + rational+ ((ε₁ /2) /2 ℚ⁺.+ ε₂ /2)
           ≈⟨ rational⁺-+ ((ε₁ /2 ℚ⁺.+ (ε₂ /2) /2) ℚ⁺.+ ((ε₁ /2) /2 ℚ⁺.+ (ε₂ /2) /2)) ((ε₁ /2) /2 ℚ⁺.+ ε₂ /2) ⟩
        rational+ ((ε₁ /2 ℚ⁺.+ (ε₂ /2) /2) ℚ⁺.+ ((ε₁ /2) /2 ℚ⁺.+ (ε₂ /2) /2) ℚ⁺.+ ((ε₁ /2) /2 ℚ⁺.+ ε₂ /2))
           ≈⟨ rational-cong (ℚ⁺.fog-cong (prove 4 (((a ⊕ b) ⊕ (c ⊕ b)) ⊕ (c ⊕ d)) ((a ⊕ (c ⊕ c)) ⊕ (d ⊕ (b ⊕ b))) (ε₁ /2 ∷ ε₂ /2 /2 ∷ ε₁ /2 /2 ∷ ε₂ /2 ∷ []))) ⟩
        rational+ ((ε₁ /2 ℚ⁺.+ (ε₁ /2 /2 ℚ⁺.+ ε₁ /2 /2)) ℚ⁺.+ (ε₂ /2 ℚ⁺.+ (ε₂ /2 /2 ℚ⁺.+ ε₂ /2 /2)))
           ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-cong (ℚ⁺.+-congʳ (ε₁ /2) (ℚ⁺.half+half {ε₁ /2})) (ℚ⁺.+-congʳ (ε₂ /2) (ℚ⁺.half+half {ε₂ /2})))) ⟩
        rational+ ((ε₁ /2 ℚ⁺.+ ε₁ /2) ℚ⁺.+ (ε₂ /2 ℚ⁺.+ ε₂ /2))
           ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-cong (ℚ⁺.half+half {ε₁}) (ℚ⁺.half+half {ε₂}))) ⟩
        rational+ (ε₁ ℚ⁺.+ ε₂)
        --    ≈⟨ ≃-sym (+-identityˡ (rational+ (ε₁ ℚ⁺.+ ε₂))) ⟩
        -- 0ℝ + rational+ (ε₁ ℚ⁺.+ ε₂)
      ∎

------------------------------------------------------------------------------
-- Idempotency
--
--  This shows that    join : 𝒞 (𝒞 X) ≅ 𝒞 X : unit

unit-join : ∀ {X} → (unit ∘ join) ≈f id {𝒞 (𝒞 X)}
unit-join .f≈f x =
  sup-least λ { (ε₁ , ε₂) →
     ⊖-iso2 (sup-least λ { (ε₁' , ε₂') →
        ⊖-iso2 (≤-trans (⊖-iso1 (≤-trans (sup-upper (ε₁' /2 , ε₂')) (x .regular (ε₁' /2) ε₂))) (ineq ε₁ ε₂ ε₁' ε₂')) }) }
  where
    open ≤-Reasoning
    open import CommutativeSemigroupSolver (ℚ⁺.+-commutativeSemigroup)
    a = v# 0; b = v# 1; c = v# 2; d = v# 3
    ineq : ∀ ε₁ ε₂ ε₁' ε₂' → (rational+ (ε₁' /2 ℚ⁺.+ ε₂) + rational+ (ε₁' /2 ℚ⁺.+ ε₂')) ≤ ((0ℝ + rational+ (ε₁ ℚ⁺.+ ε₂)) + rational+ (ε₁' ℚ⁺.+ ε₂'))
    ineq ε₁ ε₂ ε₁' ε₂' =
      begin
        rational+ (ε₁' /2 ℚ⁺.+ ε₂) + rational+ (ε₁' /2 ℚ⁺.+ ε₂')
          ≈⟨ rational⁺-+ (ε₁' /2 ℚ⁺.+ ε₂) (ε₁' /2 ℚ⁺.+ ε₂') ⟩
        rational+ ((ε₁' /2 ℚ⁺.+ ε₂) ℚ⁺.+ (ε₁' /2 ℚ⁺.+ ε₂'))
          ≈⟨ rational-cong (ℚ⁺.fog-cong (prove 3 ((a ⊕ b) ⊕ (a ⊕ c)) (b ⊕ ((a ⊕ a) ⊕ c)) (ε₁' /2 ∷ ε₂ ∷ ε₂' ∷ []))) ⟩
        rational+ (ε₂ ℚ⁺.+ ((ε₁' /2 ℚ⁺.+ ε₁' /2) ℚ⁺.+ ε₂'))
          ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-congʳ ε₂ (ℚ⁺.+-congˡ ε₂' (ℚ⁺.half+half {ε₁'}))))  ⟩
        rational+ (ε₂ ℚ⁺.+ (ε₁' ℚ⁺.+ ε₂'))
          ≤⟨ rational-mono (ℚ⁺.fog-mono (ℚ⁺.+-mono-≤ (ℚ⁺.+-increasing {ε₂} {ε₁}) (ℚ⁺.≤-refl {ε₁' ℚ⁺.+ ε₂'}))) ⟩
        rational+ ((ε₂ ℚ⁺.+ ε₁) ℚ⁺.+ (ε₁' ℚ⁺.+ ε₂'))
          ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-congˡ (ε₁' ℚ⁺.+ ε₂') (ℚ⁺.+-comm ε₂ ε₁))) ⟩
        rational+ ((ε₁ ℚ⁺.+ ε₂) ℚ⁺.+ (ε₁' ℚ⁺.+ ε₂'))
          ≈⟨ ≃-sym (rational⁺-+ (ε₁ ℚ⁺.+ ε₂) (ε₁' ℚ⁺.+ ε₂')) ⟩
        rational+ (ε₁ ℚ⁺.+ ε₂) + rational+ (ε₁' ℚ⁺.+ ε₂')
          ≈⟨ +-cong (≃-sym (+-identityˡ (rational+ (ε₁ ℚ⁺.+ ε₂)))) ≃-refl ⟩
        (0ℝ + rational+ (ε₁ ℚ⁺.+ ε₂)) + rational+ (ε₁' ℚ⁺.+ ε₂')
      ∎

------------------------------------------------------------------------------
-- This is a monoidal monad, with respect to the monoidal product

open import metric2.monoidal

monoidal-⊗ : ∀ {X Y} → (𝒞 X ⊗ 𝒞 Y) ⇒ 𝒞 (X ⊗ Y)
monoidal-⊗ .fun (x , y) .rfun ε = x .rfun (ε /2) , y .rfun (ε /2)
monoidal-⊗ {X}{Y} .fun (x , y) .regular ε₁ ε₂ =
  begin
    (X .dist (x .rfun (ε₁ /2)) (x .rfun (ε₂ /2)) + Y .dist (y .rfun (ε₁ /2)) (y .rfun (ε₂ /2)))
      ≤⟨ +-mono-≤ (x .regular (ε₁ /2) (ε₂ /2)) (y .regular (ε₁ /2) (ε₂ /2)) ⟩
    rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)
      ≈⟨ rational⁺-+ (ε₁ /2 ℚ⁺.+ ε₂ /2) (ε₁ /2 ℚ⁺.+ ε₂ /2) ⟩
    rational+ ((ε₁ /2 ℚ⁺.+ ε₂ /2) ℚ⁺.+ (ε₁ /2 ℚ⁺.+ ε₂ /2))
      ≤⟨ rational-mono (ℚ⁺.fog-mono (ℚ⁺.≤-reflexive (ℚ⁺-interchange (ε₁ /2) (ε₂ /2) (ε₁ /2) (ε₂ /2)))) ⟩
    rational+ ((ε₁ /2 ℚ⁺.+ ε₁ /2) ℚ⁺.+ (ε₂ /2 ℚ⁺.+ ε₂ /2))
      ≤⟨ rational-mono (ℚ⁺.fog-mono (ℚ⁺.≤-reflexive (ℚ⁺.+-cong (ℚ⁺.half+half {ε₁}) (ℚ⁺.half+half {ε₂})))) ⟩
    rational+ (ε₁ ℚ⁺.+ ε₂)
  ∎
  where open ≤-Reasoning
monoidal-⊗ {X}{Y} .non-expansive {x₁ , y₁} {x₂ , y₂} =
  sup-least λ { (ε₁ , ε₂) → ⊖-iso2
    (begin
      X .dist (x₁ .rfun (ε₁ /2)) (x₂ .rfun (ε₂ /2)) + Y .dist (y₁ .rfun (ε₁ /2)) (y₂ .rfun (ε₂ /2))
          ≤⟨ +-mono-≤ ⊖-eval ⊖-eval ⟩
        ((X .dist (x₁ .rfun (ε₁ /2)) (x₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2))
      + ((Y .dist (y₁ .rfun (ε₁ /2)) (y₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2))
          ≈⟨ interchange (X .dist (x₁ .rfun (ε₁ /2)) (x₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) (rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2))
                         (Y .dist (y₁ .rfun (ε₁ /2)) (y₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)) (rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)) ⟩
     ( (X .dist (x₁ .rfun (ε₁ /2)) (x₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2))
      + (Y .dist (y₁ .rfun (ε₁ /2)) (y₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)))
      + (rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2))
          ≈⟨ +-cong ≃-refl (rational⁺-+ (ε₁ /2 ℚ⁺.+ ε₂ /2) (ε₁ /2 ℚ⁺.+ ε₂ /2)) ⟩
     ( (X .dist (x₁ .rfun (ε₁ /2)) (x₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2))
      + (Y .dist (y₁ .rfun (ε₁ /2)) (y₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)))
      + (rational+ ((ε₁ /2 ℚ⁺.+ ε₂ /2) ℚ⁺.+ (ε₁ /2 ℚ⁺.+ ε₂ /2)))
          ≤⟨ +-mono-≤ ≤-refl (rational-mono (ℚ⁺.fog-mono (ℚ⁺.≤-reflexive (ℚ⁺-interchange (ε₁ /2) (ε₂ /2) (ε₁ /2) (ε₂ /2))))) ⟩
     ( (X .dist (x₁ .rfun (ε₁ /2)) (x₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2))
      + (Y .dist (y₁ .rfun (ε₁ /2)) (y₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2)))
      + (rational+ ((ε₁ /2 ℚ⁺.+ ε₁ /2) ℚ⁺.+ (ε₂ /2 ℚ⁺.+ ε₂ /2)))
          ≤⟨ +-mono-≤ ≤-refl (rational-mono (ℚ⁺.fog-mono (ℚ⁺.≤-reflexive (ℚ⁺.+-cong (ℚ⁺.half+half {ε₁}) (ℚ⁺.half+half {ε₂}))))) ⟩
      (  (X .dist (x₁ .rfun (ε₁ /2)) (x₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2))
       + (Y .dist (y₁ .rfun (ε₁ /2)) (y₂ .rfun (ε₂ /2)) ⊖ (ε₁ /2 ℚ⁺.+ ε₂ /2))) + rational+ (ε₁ ℚ⁺.+ ε₂)
          ≤⟨ +-mono-≤ (+-mono-≤ (sup-upper (ε₁ /2 , ε₂ /2)) (sup-upper (ε₁ /2 , ε₂ /2))) ≤-refl ⟩
      (reg-dist x₁ x₂ + reg-dist y₁ y₂) + rational+ (ε₁ ℚ⁺.+ ε₂)
    ∎) }
  where open ≤-Reasoning

monoidal-natural : ∀ {X X' Y Y'} → (f : X ⇒ X') (g : Y ⇒ Y') →
                   (monoidal-⊗ ∘ (map f ⊗f map g)) ≈f (map (f ⊗f g) ∘ monoidal-⊗)
monoidal-natural {X}{X'}{Y}{Y'} f g .f≈f (x , y) =
  sup-least λ { (ε₁ , ε₂) → ⊖-iso2
    (begin
      X' .dist (f .fun (x .rfun (ε₁ /2))) (f .fun (x .rfun (ε₂ /2))) + Y' .dist (g .fun (y .rfun (ε₁ /2))) (g .fun (y .rfun (ε₂ /2)))
    ≤⟨ +-mono-≤ (f .non-expansive) (g .non-expansive) ⟩
      (X .dist (x .rfun (ε₁ /2)) (x .rfun (ε₂ /2)) + Y .dist (y .rfun (ε₁ /2)) (y .rfun (ε₂ /2)))
    ≤⟨ +-mono-≤ (x .regular (ε₁ /2) (ε₂ /2)) (y .regular (ε₁ /2) (ε₂ /2)) ⟩
      rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)
    ≈⟨ rational⁺-+ (ε₁ /2 ℚ⁺.+ ε₂ /2) (ε₁ /2 ℚ⁺.+ ε₂ /2) ⟩
      rational+ ((ε₁ /2 ℚ⁺.+ ε₂ /2) ℚ⁺.+ (ε₁ /2 ℚ⁺.+ ε₂ /2))
    ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺-interchange (ε₁ /2) (ε₂ /2) (ε₁ /2) (ε₂ /2))) ⟩
      rational+ ((ε₁ /2 ℚ⁺.+ ε₁ /2) ℚ⁺.+ (ε₂ /2 ℚ⁺.+ ε₂ /2))
    ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-cong (ℚ⁺.half+half {ε₁}) (ℚ⁺.half+half {ε₂}))) ⟩
      rational+ (ε₁ ℚ⁺.+ ε₂)
    ≈⟨ ≃-sym (+-identityˡ (rational+ (ε₁ ℚ⁺.+ ε₂))) ⟩
      0ℝ + rational+ (ε₁ ℚ⁺.+ ε₂)
    ∎) }
  where open ≤-Reasoning

monoidal-assoc : ∀ {X Y Z} →
  (monoidal-⊗ ∘ (monoidal-⊗ ⊗f id) ∘ ⊗-assoc {𝒞 X} {𝒞 Y} {𝒞 Z}) ≈f (map ⊗-assoc ∘ monoidal-⊗ ∘ (id ⊗f monoidal-⊗))
monoidal-assoc {X}{Y}{Z} .f≈f (x , (y , z)) =
  sup-least λ { (ε₁ , ε₂) → ⊖-iso2
    (begin
      (X .dist (x .rfun ((ε₁ /2) /2)) (x .rfun (ε₂ /2)) + Y .dist (y .rfun ((ε₁ /2) /2)) (y .rfun ((ε₂ /2) /2))) + Z .dist (z .rfun (ε₁ /2)) (z .rfun ((ε₂ /2) /2))
    ≤⟨ +-mono-≤ (+-mono-≤ (x .regular (ε₁ /2 /2) (ε₂ /2)) (y .regular (ε₁ /2 /2) (ε₂ /2 /2))) (z .regular (ε₁ /2) (ε₂ /2 /2)) ⟩
      (rational+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2) + rational+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2)) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2 /2)
    ≈⟨ +-cong (rational⁺-+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2) (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2)) ≃-refl ⟩
      rational+ ((ε₁ /2 /2 ℚ⁺.+ ε₂ /2) ℚ⁺.+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2)) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2 /2)
    ≈⟨ rational⁺-+ ((ε₁ /2 /2 ℚ⁺.+ ε₂ /2) ℚ⁺.+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2)) (ε₁ /2 ℚ⁺.+ ε₂ /2 /2) ⟩
      rational+ (((ε₁ /2 /2 ℚ⁺.+ ε₂ /2) ℚ⁺.+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2)) ℚ⁺.+ (ε₁ /2 ℚ⁺.+ ε₂ /2 /2))
    ≈⟨ rational-cong (ℚ⁺.fog-cong
        (prove 4 (((b ⊕ c) ⊕ (b ⊕ d)) ⊕ (a ⊕ d)) ((a ⊕ (b ⊕ b)) ⊕ (c ⊕ (d ⊕ d))) (ε₁ /2 ∷ ε₁ /2 /2 ∷ ε₂ /2 ∷ ε₂ /2 /2 ∷ []))) ⟩
      rational+ ((ε₁ /2 ℚ⁺.+ (ε₁ /2 /2 ℚ⁺.+ ε₁ /2 /2)) ℚ⁺.+ (ε₂ /2 ℚ⁺.+ (ε₂ /2 /2 ℚ⁺.+ ε₂ /2 /2)))
    ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-cong (ℚ⁺.+-congʳ (ε₁ /2) (ℚ⁺.half+half {ε₁ /2})) (ℚ⁺.+-congʳ (ε₂ /2) (ℚ⁺.half+half {ε₂ /2})))) ⟩
      rational+ ((ε₁ /2 ℚ⁺.+ ε₁ /2) ℚ⁺.+ (ε₂ /2 ℚ⁺.+ ε₂ /2))
    ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-cong (ℚ⁺.half+half {ε₁}) (ℚ⁺.half+half {ε₂}))) ⟩
      rational+ (ε₁ ℚ⁺.+ ε₂)
    ≈⟨ ≃-sym (+-identityˡ (rational+ (ε₁ ℚ⁺.+ ε₂))) ⟩
      0ℝ + rational+ (ε₁ ℚ⁺.+ ε₂)
    ∎) }
  where open ≤-Reasoning
        open import CommutativeSemigroupSolver (ℚ⁺.+-commutativeSemigroup)
        a = v# 0; b = v# 1; c = v# 2; d = v# 3

monoidal-symmetry : ∀ {X Y} →
  (monoidal-⊗ {Y} {X} ∘ ⊗-symmetry) ≈f (map ⊗-symmetry ∘ monoidal-⊗)
monoidal-symmetry {X}{Y} .f≈f (x , y) =
  sup-least λ { (ε₁ , ε₂) → ⊖-iso2
    (begin
      Y .dist (y .rfun (ε₁ /2)) (y .rfun (ε₂ /2)) + X .dist (x .rfun (ε₁ /2)) (x .rfun (ε₂ /2))
     ≤⟨ +-mono-≤ (y .regular (ε₁ /2) (ε₂ /2)) (x .regular (ε₁ /2) (ε₂ /2)) ⟩
      rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)
    ≈⟨ rational⁺-+ (ε₁ /2 ℚ⁺.+ ε₂ /2) (ε₁ /2 ℚ⁺.+ ε₂ /2) ⟩
      rational+ ((ε₁ /2 ℚ⁺.+ ε₂ /2) ℚ⁺.+ (ε₁ /2 ℚ⁺.+ ε₂ /2))
    ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺-interchange (ε₁ /2) (ε₂ /2) (ε₁ /2) (ε₂ /2))) ⟩
      rational+ ((ε₁ /2 ℚ⁺.+ ε₁ /2) ℚ⁺.+ (ε₂ /2 ℚ⁺.+ ε₂ /2))
    ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-cong (ℚ⁺.half+half {ε₁}) (ℚ⁺.half+half {ε₂}))) ⟩
      rational+ (ε₁ ℚ⁺.+ ε₂)
    ≈⟨ ≃-sym (+-identityˡ (rational+ (ε₁ ℚ⁺.+ ε₂))) ⟩
      0ℝ + rational+ (ε₁ ℚ⁺.+ ε₂)
    ∎)
  }
  where open ≤-Reasoning

monoidal-unit : ∀ {X Y} → (monoidal-⊗ {X} {Y} ∘ (unit ⊗f unit)) ≈f unit
monoidal-unit {X}{Y} .f≈f (x , y) =
  sup-least (λ { (ε₁ , ε₂) → ⊖-iso2
    (begin
      X .dist x x + Y .dist y y
    ≤⟨ +-mono-≤ (X .refl) (Y .refl) ⟩
      0ℝ + 0ℝ
    ≤⟨ +-mono-≤ ≤-refl (0-least (rational+ (ε₁ ℚ⁺.+ ε₂))) ⟩
      0ℝ + rational+ (ε₁ ℚ⁺.+ ε₂)
    ∎) })
  where open ≤-Reasoning

monoidal-join : ∀ {X Y} → (monoidal-⊗ {X}{Y} ∘ (join ⊗f join)) ≈f (join ∘ map monoidal-⊗ ∘ monoidal-⊗)
monoidal-join {X}{Y} .f≈f (x , y) =
  𝒞-≈ {X ⊗ Y} {monoidal-⊗ .fun (join .fun x , join .fun y)}
    {join .fun (map monoidal-⊗ .fun (monoidal-⊗ .fun (x , y)))}
  λ ε₁ ε₂ →
  begin
      X .dist (x .rfun ((ε₁ /2) /2) .rfun ((ε₁ /2) /2)) (x .rfun ((ε₂ /2) /2) .rfun ((ε₂ /2) /2))
    + Y .dist (y .rfun ((ε₁ /2) /2) .rfun ((ε₁ /2) /2)) (y .rfun ((ε₂ /2) /2) .rfun ((ε₂ /2) /2))
  ≤⟨ +-mono-≤ (⊖-iso1 (≤-trans (sup-upper (ε₁ /2 /2 , ε₂ /2 /2)) (x .regular (ε₁ /2 /2) (ε₂ /2 /2))))
              (⊖-iso1 (≤-trans (sup-upper (ε₁ /2 /2 , ε₂ /2 /2)) (y .regular (ε₁ /2 /2) (ε₂ /2 /2)))) ⟩
    (rational+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2) + rational+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2)) + (rational+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2) + rational+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2))
  ≈⟨ +-cong (rational⁺-+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2) (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2)) (rational⁺-+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2) (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2)) ⟩
    rational+ ((ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2) ℚ⁺.+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2)) + rational+ ((ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2) ℚ⁺.+ (ε₁ /2 /2 ℚ⁺.+ ε₂ /2 /2))
  ≈⟨ +-cong (rational-cong (ℚ⁺.fog-cong (ℚ⁺-interchange (ε₁ /2 /2) (ε₂ /2 /2) (ε₁ /2 /2) (ε₂ /2 /2))))
            (rational-cong (ℚ⁺.fog-cong (ℚ⁺-interchange (ε₁ /2 /2) (ε₂ /2 /2) (ε₁ /2 /2) (ε₂ /2 /2)))) ⟩
    rational+ ((ε₁ /2 /2 ℚ⁺.+ ε₁ /2 /2) ℚ⁺.+ (ε₂ /2 /2 ℚ⁺.+ ε₂ /2 /2)) + rational+ ((ε₁ /2 /2 ℚ⁺.+ ε₁ /2 /2) ℚ⁺.+ (ε₂ /2 /2 ℚ⁺.+ ε₂ /2 /2))
  ≈⟨ +-cong (rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-cong (ℚ⁺.half+half {ε₁ /2}) (ℚ⁺.half+half {ε₂ /2}))))
            (rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-cong (ℚ⁺.half+half {ε₁ /2}) (ℚ⁺.half+half {ε₂ /2})))) ⟩
    rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2) + rational+ (ε₁ /2 ℚ⁺.+ ε₂ /2)
  ≈⟨ rational⁺-+ (ε₁ /2 ℚ⁺.+ ε₂ /2) (ε₁ /2 ℚ⁺.+ ε₂ /2) ⟩
    rational+ ((ε₁ /2 ℚ⁺.+ ε₂ /2) ℚ⁺.+ (ε₁ /2 ℚ⁺.+ ε₂ /2))
  ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺-interchange (ε₁ /2) (ε₂ /2) (ε₁ /2) (ε₂ /2))) ⟩
    rational+ ((ε₁ /2 ℚ⁺.+ ε₁ /2) ℚ⁺.+ (ε₂ /2 ℚ⁺.+ ε₂ /2))
  ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.+-cong (ℚ⁺.half+half {ε₁}) (ℚ⁺.half+half {ε₂}))) ⟩
    rational+ (ε₁ ℚ⁺.+ ε₂)
  ∎
  where open ≤-Reasoning

{-
monoidal-⊗⁻¹ : ∀ {X Y} → 𝒞 (X ⊗ Y) ⇒ (𝒞 X ⊗ 𝒞 Y)
monoidal-⊗⁻¹ .fun x .proj₁ .rfun ε = x .rfun ε .proj₁
monoidal-⊗⁻¹ .fun x .proj₁ .regular ε₁ ε₂ = {!!}
monoidal-⊗⁻¹ .fun x .proj₂ .rfun ε = x .rfun ε .proj₂
monoidal-⊗⁻¹ .fun x .proj₂ .regular ε₁ ε₂ = {!!}
monoidal-⊗⁻¹ .non-expansive = {!!}
-}

------------------------------------------------------------------------------
open import metric2.scaling

distr : ∀ {X} q → ![ q ] (𝒞 X) ⇒ 𝒞 (![ q ] X)
distr {X} q .fun x .rfun ε = x .rfun (1/ q ℚ⁺.* ε)
distr {X} q .fun x .regular ε₁ ε₂ =
  begin
    rational+ q * X .dist (x .rfun (1/ q ℚ⁺.* ε₁)) (x .rfun (1/ q ℚ⁺.* ε₂))
  ≤⟨ *-mono-≤ ≤-refl (x .regular (1/ q ℚ⁺.* ε₁) (1/ q ℚ⁺.* ε₂)) ⟩
    rational+ q * rational+ ((1/ q ℚ⁺.* ε₁) ℚ⁺.+ (1/ q ℚ⁺.* ε₂))
  ≈⟨ *-cong ≃-refl (rational-cong (ℚ⁺.fog-cong (ℚ⁺.≃-sym (ℚ⁺.*-distribˡ-+ (1/ q) ε₁ ε₂)))) ⟩
    rational+ q * rational+ (1/ q ℚ⁺.* (ε₁ ℚ⁺.+ ε₂))
  ≈⟨ rational⁺-* q (1/ q ℚ⁺.* (ε₁ ℚ⁺.+ ε₂)) ⟩
    rational+ (q ℚ⁺.* (1/ q ℚ⁺.* (ε₁ ℚ⁺.+ ε₂)))
  ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.≃-sym (ℚ⁺.*-assoc q (1/ q) (ε₁ ℚ⁺.+ ε₂)))) ⟩
    rational+ ((q ℚ⁺.* 1/ q) ℚ⁺.* (ε₁ ℚ⁺.+ ε₂))
  ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.*-cong (ℚ⁺.*-inverseʳ q) (ℚ⁺.≃-refl {ε₁ ℚ⁺.+ ε₂}))) ⟩
    rational+ (1ℚ⁺ ℚ⁺.* (ε₁ ℚ⁺.+ ε₂))
  ≈⟨ rational-cong (ℚ⁺.fog-cong (ℚ⁺.*-identityˡ (ε₁ ℚ⁺.+ ε₂))) ⟩
    rational+ (ε₁ ℚ⁺.+ ε₂)
  ∎
  where open ≤-Reasoning
distr {X} q .non-expansive {x} {y} =
  sup-least λ { (ε₁ , ε₂)  → ⊖-iso2
    (begin
      rational+ q * X .dist (x .rfun (1/ q ℚ⁺.* ε₁)) (y .rfun (1/ q ℚ⁺.* ε₂))
    ≤⟨ *-mono-≤ ≤-refl ⊖-eval ⟩
      rational+ q * ((X .dist (x .rfun (1/ q ℚ⁺.* ε₁)) (y .rfun (1/ q ℚ⁺.* ε₂)) ⊖ ((1/ q ℚ⁺.* ε₁) ℚ⁺.+ (1/ q ℚ⁺.* ε₂))) + rational+ ((1/ q ℚ⁺.* ε₁) ℚ⁺.+ (1/ q ℚ⁺.* ε₂)))
    ≈⟨ *-distribˡ-+ (rational+ q)
                   (X .dist (x .rfun (1/ q ℚ⁺.* ε₁)) (y .rfun (1/ q ℚ⁺.* ε₂)) ⊖ ((1/ q ℚ⁺.* ε₁) ℚ⁺.+ (1/ q ℚ⁺.* ε₂)))
                   (rational+ ((1/ q ℚ⁺.* ε₁) ℚ⁺.+ (1/ q ℚ⁺.* ε₂))) ⟩
      (rational+ q * (X .dist (x .rfun (1/ q ℚ⁺.* ε₁)) (y .rfun (1/ q ℚ⁺.* ε₂)) ⊖ ((1/ q ℚ⁺.* ε₁) ℚ⁺.+ (1/ q ℚ⁺.* ε₂)))) +
      (rational+ q * rational+ ((1/ q ℚ⁺.* ε₁) ℚ⁺.+ (1/ q ℚ⁺.* ε₂)))
    ≤⟨ +-mono-≤ (*-mono-≤ ≤-refl (sup-upper (1/ q ℚ⁺.* ε₁ , 1/ q ℚ⁺.* ε₂))) ≤-refl ⟩
      dist (![ q ] (𝒞 X)) x y + (rational+ q * rational+ ((1/ q ℚ⁺.* ε₁) ℚ⁺.+ (1/ q ℚ⁺.* ε₂)))
    ≈⟨ +-cong ≃-refl (rational⁺-* q ((1/ q ℚ⁺.* ε₁) ℚ⁺.+ (1/ q ℚ⁺.* ε₂))) ⟩
      dist (![ q ] (𝒞 X)) x y + rational+ (q ℚ⁺.* ((1/ q ℚ⁺.* ε₁) ℚ⁺.+ (1/ q ℚ⁺.* ε₂)))
    ≈⟨ +-cong ≃-refl (rational-cong (ℚ⁺.fog-cong (ℚ⁺.*-cong (ℚ⁺.≃-refl {q}) (ℚ⁺.≃-sym (ℚ⁺.*-distribˡ-+ (1/ q) ε₁ ε₂))))) ⟩
      dist (![ q ] (𝒞 X)) x y + rational+ (q ℚ⁺.* (1/ q ℚ⁺.* (ε₁ ℚ⁺.+ ε₂)))
    ≈⟨ +-cong ≃-refl (rational-cong (ℚ⁺.fog-cong (ℚ⁺.≃-sym (ℚ⁺.*-assoc q (1/ q) (ε₁ ℚ⁺.+ ε₂))))) ⟩
      dist (![ q ] (𝒞 X)) x y + rational+ ((q ℚ⁺.* 1/ q) ℚ⁺.* (ε₁ ℚ⁺.+ ε₂))
    ≈⟨ +-cong ≃-refl (rational-cong (ℚ⁺.fog-cong (ℚ⁺.*-cong (ℚ⁺.*-inverseʳ q) (ℚ⁺.≃-refl {ε₁ ℚ⁺.+ ε₂})))) ⟩
      dist (![ q ] (𝒞 X)) x y + rational+ (1ℚ⁺ ℚ⁺.* (ε₁ ℚ⁺.+ ε₂))
    ≈⟨ +-cong ≃-refl (rational-cong (ℚ⁺.fog-cong (ℚ⁺.*-identityˡ (ε₁ ℚ⁺.+ ε₂)))) ⟩
      dist (![ q ] (𝒞 X)) x y + rational+ (ε₁ ℚ⁺.+ ε₂)
    ∎) }
  where open ≤-Reasoning
