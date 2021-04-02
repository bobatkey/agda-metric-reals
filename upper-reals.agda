module upper-reals where

open import Level using (0ℓ; suc)
open import Algebra using (CommutativeSemigroup; Commutative; Congruent₂; LeftIdentity; RightIdentity; Associative)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥)
open import Data.Rational.Unnormalised as ℚ using () renaming (ℚᵘ to ℚ; 0ℚᵘ to 0ℚ; 1ℚᵘ to 1ℚ)
import Data.Rational.Unnormalised.Properties as ℚ
open import Relation.Nullary using (yes; no; ¬_)
import Relation.Nullary.Decidable as Dec
import Data.Rational.Unnormalised.Solver as ℚSolver
open import Relation.Binary using (Antisymmetric; IsEquivalence; IsPreorder; IsPartialOrder; Poset; _Preserves₂_⟶_⟶_)

import qpos
open import qpos as ℚ⁺ using (ℚ⁺; _/2; 1/_)

module interchange {c ℓ} (G : CommutativeSemigroup c ℓ)  where
  open CommutativeSemigroup G
  open import Relation.Binary.Reasoning.Setoid setoid

  interchange : ∀ a b c d → (a ∙ b) ∙ (c ∙ d) ≈ (a ∙ c) ∙ (b ∙ d)
  interchange a b c d =
    begin
      (a ∙ b) ∙ (c ∙ d)
        ≈⟨ assoc a b (c ∙ d) ⟩
      a ∙ (b ∙ (c ∙ d))
        ≈⟨ ∙-congˡ (sym (assoc b c d)) ⟩
      a ∙ ((b ∙ c) ∙ d)
        ≈⟨ ∙-congˡ (∙-congʳ (comm b c)) ⟩
      a ∙ ((c ∙ b) ∙ d)
        ≈⟨ ∙-congˡ (assoc c b d) ⟩
      a ∙ (c ∙ (b ∙ d))
        ≈⟨ sym (assoc a c (b ∙ d)) ⟩
      (a ∙ c) ∙ (b ∙ d)
    ∎

open interchange (qpos.+-commutativeSemigroup) renaming (interchange to ℚ⁺-interchange) public
open interchange (record
                    { isCommutativeSemigroup = record { isSemigroup = ℚ.+-isSemigroup ; comm = ℚ.+-comm } }) renaming (interchange to ℚ-interchange) public

-- an upper real is a set of upper bounds on a real number
record ℝᵘ : Set₁ where
  no-eta-equality -- FIXME: this seems to speed things up considerably, and makes goals easier to read
  field
    contains : ℚ⁺ → Set
    upper    : ∀ {q₁ q₂} → q₁ ℚ⁺.≤ q₂ → contains q₁ → contains q₂
    closed   : ∀ {q} → (∀ r → contains (q ℚ⁺.+ r)) → contains q
  -- FIXME: do we need locatedness?
open ℝᵘ

-- FIXME: why not rounded sets?

------------------------------------------------------------------------------
record _≤_ (x y : ℝᵘ) : Set where
  field
    *≤* : ∀ {q} → y .contains q → x .contains q
open _≤_

≤-refl : ∀ {x} → x ≤ x
≤-refl .*≤* x-q = x-q

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans x≤y y≤z .*≤* = λ z-q → x≤y .*≤* (y≤z .*≤* z-q)

_≃_ : ℝᵘ → ℝᵘ → Set
x ≃ y = x ≤ y × y ≤ x

≃-refl : ∀ {x} → x ≃ x
≃-refl {x} = ≤-refl {x} , ≤-refl {x}

≃-sym : ∀ {x y} → x ≃ y → y ≃ x
≃-sym (x≤y , y≤x) = y≤x , x≤y

≃-trans : ∀ {x y z} → x ≃ y → y ≃ z → x ≃ z
≃-trans (x≤y , y≤x) (y≤z , z≤y) = ≤-trans x≤y y≤z , ≤-trans z≤y y≤x

≤-reflexive : ∀ {x y} → x ≃ y → x ≤ y
≤-reflexive x≃y = x≃y .proj₁

≤-antisym : Antisymmetric _≃_ _≤_
≤-antisym i≤j j≤i = i≤j , j≤i

isEquivalence : IsEquivalence _≃_
isEquivalence = record { refl = ≃-refl ; sym = ≃-sym ; trans = ≃-trans }

isPreOrder : IsPreorder _≃_ _≤_
isPreOrder = record { isEquivalence = isEquivalence ; reflexive = ≤-reflexive ; trans = ≤-trans }

isPartialOrder : IsPartialOrder _≃_ _≤_
isPartialOrder = record { isPreorder = isPreOrder ; antisym = ≤-antisym }

poset : Poset (suc 0ℓ) 0ℓ 0ℓ
poset = record { isPartialOrder = isPartialOrder }

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.PartialOrder poset public

------------------------------------------------------------------------------
_<_ : ℝᵘ → ℝᵘ → Set
x < y = Σ[ q ∈ ℚ⁺ ] (x .contains q × ¬ y .contains q)

-- FIXME: apartness

------------------------------------------------------------------------------
-- Embedding (non negative) rationals

module closedness where
  open qpos
  open import Relation.Binary.PropositionalEquality using (refl)

  2ℚ : ℚ
  2ℚ = ℚ.1ℚᵘ ℚ.+ ℚ.1ℚᵘ

  eq : 2ℚ ℚ.* ℚ.½ ℚ.≃ 1ℚ
  eq = ℚ.*≡* refl

  p<q⇒0<q-p : ∀ {p q} → p ℚ.< q → 0ℚ ℚ.< q ℚ.- p
  p<q⇒0<q-p {p} {q} p<q = begin-strict
    0ℚ     ≈⟨ ℚ.≃-sym (ℚ.+-inverseʳ p) ⟩
    p ℚ.- p <⟨ ℚ.+-monoˡ-< (ℚ.- p) p<q ⟩
    q ℚ.- p ∎ where open ℚ.≤-Reasoning

  closed₁ : ∀ a b → (∀ ε → ε ℚ.> 0ℚ → a ℚ.≤ b ℚ.+ ε) → a ℚ.≤ b
  closed₁ a b h with a ℚ.≤? b
  ... | yes a≤b = a≤b
  ... | no ¬a≤b with ℚ.≰⇒> ¬a≤b
  ... | b<a = begin
                 a
                   ≈⟨ solve 1 (λ a → a := con 2ℚ :* a :- a) ℚ.≃-refl a ⟩
                 2ℚ ℚ.* a ℚ.- a
                   ≤⟨ mid ⟩
                 2ℚ ℚ.* (b ℚ.+ (a ℚ.- b) ℚ.* ℚ.½) ℚ.- a
                   ≈⟨ solve 3 (λ a b c → con 2ℚ :* (b :+ (a :- b) :* c) :- a := con 2ℚ :* b :+ (a :- b) :* (con 2ℚ :* c) :- a)
                        ℚ.≃-refl a b ℚ.½ ⟩
                 2ℚ ℚ.* b ℚ.+ (a ℚ.- b) ℚ.* (2ℚ ℚ.* ℚ.½) ℚ.- a
                   ≈⟨ ℚ.+-congˡ (ℚ.- a) (ℚ.+-congʳ (2ℚ ℚ.* b) (ℚ.*-cong (ℚ.≃-refl {a ℚ.- b}) eq)) ⟩
                 2ℚ ℚ.* b ℚ.+ (a ℚ.- b) ℚ.* 1ℚ ℚ.- a
                   ≈⟨ solve 2 (λ a b → con 2ℚ :* b :+ (a :- b) :* con 1ℚ :- a := b) ℚ.≃-refl a b ⟩
                 b
               ∎
    where
     open ℚ.≤-Reasoning
     open ℚSolver.+-*-Solver

     foop : 0ℚ ℚ.< (a ℚ.- b) ℚ.* ℚ.½
     foop = ℚ.≤-<-trans (ℚ.≤-reflexive (ℚ.*≡* refl)) (ℚ.*-monoˡ-<-pos {ℚ.½} tt (p<q⇒0<q-p b<a))

     mid : 2ℚ ℚ.* a ℚ.- a ℚ.≤ 2ℚ ℚ.* (b ℚ.+ (a ℚ.- b) ℚ.* ℚ.½) ℚ.- a
     mid = ℚ.+-monoˡ-≤ (ℚ.- a) (ℚ.*-monoʳ-≤-nonNeg {2ℚ} tt (h ((a ℚ.- b) ℚ.* ℚ.½) foop))

  closed' : ∀ a b → (∀ ε → a ℚ.≤ fog (b + ε)) → a ℚ.≤ fog b
  closed' a b h =
    closed₁ a (fog b) λ ε ε>0 → begin
                                 a                         ≤⟨ h (gof ε ε>0) ⟩
                                 fog (b + gof ε ε>0)       ≈⟨ ℚ.*≡* refl ⟩
                                 fog b ℚ.+ ε ∎
      where open ℚ.≤-Reasoning


-- should be a group homomorphism and lattice homomorphism
rational : ℚ → ℝᵘ -- FIXME: should be ℚ̂≥0
rational r .contains q = r ℚ.≤ ℚ⁺.fog q
rational r .upper q₁≤q₂ r≤q₁ = ℚ.≤-trans r≤q₁ (ℚ⁺.fog-mono q₁≤q₂)
rational r .closed {q} = closedness.closed' r q

rational-mono : ∀ {q r} → q ℚ.≤ r → rational q ≤ rational r
rational-mono q≤r .*≤* = ℚ.≤-trans q≤r

rational-cong : ∀ {q r} → q ℚ.≃ r → rational q ≃ rational r
rational-cong q≃r .proj₁ = rational-mono (ℚ.≤-reflexive q≃r)
rational-cong q≃r .proj₂ = rational-mono (ℚ.≤-reflexive (ℚ.≃-sym q≃r))

rational+ : ℚ⁺ → ℝᵘ
rational+ q = rational (ℚ⁺.fog q)

0ℝ : ℝᵘ
0ℝ .contains q = ⊤
0ℝ .upper _ tt = tt
0ℝ .closed _ = tt

0-least : ∀ x → 0ℝ ≤ x
0-least x .*≤* _ = tt

∞ : ℝᵘ
∞ .contains q = ⊥
∞ .upper _ ()
∞ .closed {q} h = h q

∞-greatest : ∀ x → x ≤ ∞
∞-greatest x .*≤* ()

module binary-op (_⚈_ : ℚ⁺ → ℚ⁺ → ℚ⁺)
                 (⚈-comm : Commutative ℚ⁺._≃_ _⚈_)
      where

  _⚈ℝ_ : ℝᵘ → ℝᵘ → ℝᵘ
  (x ⚈ℝ y) .contains q = ∀ s → Σ[ q₁ ∈ ℚ⁺ ] Σ[ q₂ ∈ ℚ⁺ ] (q₁ ⚈ q₂ ℚ⁺.≤ q ℚ⁺.+ s × x .contains q₁ × y .contains q₂)
  (x ⚈ℝ y) .upper q₁≤q₂ x⚈y s =
    let q'₁ , q'₂ , ineq , x-q'₁ , y-q'₂ = x⚈y s in
    q'₁ , q'₂ , ℚ⁺.≤-trans ineq (ℚ⁺.+-mono-≤ q₁≤q₂ ℚ⁺.≤-refl) , x-q'₁ , y-q'₂
  (x ⚈ℝ y) .closed {q} h s =
    let q₁ , q₂ , ineq , x-q₁ , y-q₂ = h (s ℚ⁺./2) (s ℚ⁺./2) in
    q₁ , q₂ , ℚ⁺.≤-trans ineq (ℚ⁺.≤-reflexive (ℚ⁺.≃-trans (ℚ⁺.+-assoc q (s ℚ⁺./2) (s ℚ⁺./2)) (ℚ⁺.+-congʳ q ℚ⁺.half+half))) , x-q₁ , y-q₂

  mono-≤ : _⚈ℝ_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  mono-≤ x≤y u≤v .*≤* y⚈v s =
    let q₁ , q₂ , ineq , y-q₁ , v-q₂ = y⚈v s in
    q₁ , q₂ , ineq , x≤y .*≤* y-q₁ , u≤v .*≤* v-q₂

  cong : Congruent₂ _≃_ _⚈ℝ_
  cong {x}{y}{u}{v} x≃y u≃v =
    mono-≤ {x}{y}{u}{v} (x≃y .proj₁) (u≃v .proj₁) ,
    mono-≤ {y}{x}{v}{u} (x≃y .proj₂) (u≃v .proj₂)

  comm : Commutative _≃_ _⚈ℝ_
  comm x y .proj₁ .*≤* x⚈y s =
       let q₁ , q₂ , ineq , x-q₁ , y-q₂ = x⚈y s in
       q₂ , q₁ , ℚ⁺.≤-trans (ℚ⁺.≤-reflexive (⚈-comm q₂ q₁)) ineq , y-q₂ , x-q₁
  comm x y .proj₂ .*≤* x⚈y s =
       let q₁ , q₂ , ineq , x-q₁ , y-q₂ = x⚈y s in
       q₂ , q₁ , ℚ⁺.≤-trans (ℚ⁺.≤-reflexive (⚈-comm q₂ q₁)) ineq , y-q₂ , x-q₁

open binary-op (ℚ⁺._+_) (ℚ⁺.+-comm)
    renaming ( _⚈ℝ_   to _+_
             ; comm   to +-comm
             ; mono-≤ to +-mono-≤
             ; cong   to +-cong
             ) public
open binary-op (ℚ⁺._*_) (ℚ⁺.*-comm)
    renaming ( _⚈ℝ_   to _*_
             ; comm   to *-comm
             ; mono-≤ to *-mono-≤
             ; cong   to *-cong
             ) public

+-identityˡ : LeftIdentity _≃_ 0ℝ _+_
+-identityˡ x .proj₁ .*≤* {q} x-q s =
  s , q , ℚ⁺.≤-reflexive (ℚ⁺.+-comm s q) , tt , x-q
+-identityˡ x .proj₂ .*≤* {q} 0+x =
  x .closed (λ s → let q₁ , q₂ , ineq , tt , x-q₂ = 0+x s in
                    x .upper (ℚ⁺.≤-trans (ℚ⁺.≤-trans ℚ⁺.+-increasing (ℚ⁺.≤-reflexive (ℚ⁺.+-comm q₂ q₁))) ineq) x-q₂)

+-identityʳ : RightIdentity _≃_ 0ℝ _+_
+-identityʳ x = ≃-trans (+-comm x 0ℝ) (+-identityˡ x)

+-assoc : Associative _≃_ _+_
+-assoc x y z .proj₁ .*≤* {q} x+⟨y+z⟩ s =
     let q₁ , q₂ , q₁+q₂≤q+s/2 , x-q₁ , y+z = x+⟨y+z⟩ (s ℚ⁺./2) in
     let q₃ , q₄ , q₃+q₄≤q₂+s/2 , y-q₃ , z-q₄ = y+z (s ℚ⁺./2) in
     q₁ ℚ⁺.+ q₃ , q₄ ,
     (begin
       (q₁ ℚ⁺.+ q₃) ℚ⁺.+ q₄
         ≈⟨ ℚ⁺.+-assoc q₁ q₃ q₄ ⟩
       q₁ ℚ⁺.+ (q₃ ℚ⁺.+ q₄)
         ≤⟨ ℚ⁺.+-mono-≤ ℚ⁺.≤-refl q₃+q₄≤q₂+s/2 ⟩
       q₁ ℚ⁺.+ (q₂ ℚ⁺.+ s ℚ⁺./2)
         ≈⟨ ℚ⁺.≃-sym (ℚ⁺.+-assoc q₁ q₂ (s ℚ⁺./2)) ⟩
       (q₁ ℚ⁺.+ q₂) ℚ⁺.+ s ℚ⁺./2
         ≤⟨ ℚ⁺.+-mono-≤ q₁+q₂≤q+s/2 ℚ⁺.≤-refl ⟩
       (q ℚ⁺.+ s ℚ⁺./2) ℚ⁺.+ s ℚ⁺./2
         ≈⟨ ℚ⁺.+-assoc q (s ℚ⁺./2) (s ℚ⁺./2) ⟩
       q ℚ⁺.+ (s ℚ⁺./2 ℚ⁺.+ s ℚ⁺./2)
         ≈⟨ ℚ⁺.+-congʳ q ℚ⁺.half+half ⟩
       q ℚ⁺.+ s
     ∎) ,
     (λ s₁ → q₁ , q₃ , ℚ⁺.+-increasing , x-q₁ , y-q₃) , z-q₄
   where open ℚ⁺.≤-Reasoning
+-assoc x y z .proj₂ .*≤* {q} ⟨x+y⟩+z s =
     let q₁ , q₂ , q₁+q₂≤q+s/2 , x+y , z-q₂ = ⟨x+y⟩+z (s ℚ⁺./2) in
     let q₃ , q₄ , q₃+q₄≤q₁+s/2 , x-q₃ , y-q₄ = x+y (s ℚ⁺./2) in
     q₃ , q₄ ℚ⁺.+ q₂ ,
     (begin
       q₃ ℚ⁺.+ (q₄ ℚ⁺.+ q₂)
         ≈⟨ ℚ⁺.≃-sym (ℚ⁺.+-assoc q₃ q₄ q₂) ⟩
       (q₃ ℚ⁺.+ q₄) ℚ⁺.+ q₂
         ≤⟨ ℚ⁺.+-mono-≤ q₃+q₄≤q₁+s/2 ℚ⁺.≤-refl ⟩
       (q₁ ℚ⁺.+ s ℚ⁺./2) ℚ⁺.+ q₂
         ≈⟨ ℚ⁺.+-assoc q₁ (s ℚ⁺./2) q₂ ⟩
       q₁ ℚ⁺.+ (s ℚ⁺./2 ℚ⁺.+ q₂)
         ≈⟨ ℚ⁺.+-congʳ q₁ (ℚ⁺.+-comm (s ℚ⁺./2) q₂) ⟩
       q₁ ℚ⁺.+ (q₂ ℚ⁺.+ s ℚ⁺./2)
         ≈⟨ ℚ⁺.≃-sym (ℚ⁺.+-assoc q₁ q₂ (s ℚ⁺./2)) ⟩
       (q₁ ℚ⁺.+ q₂) ℚ⁺.+ s ℚ⁺./2
         ≤⟨ ℚ⁺.+-mono-≤ q₁+q₂≤q+s/2 ℚ⁺.≤-refl ⟩
       (q ℚ⁺.+ s ℚ⁺./2) ℚ⁺.+ s ℚ⁺./2
         ≈⟨ ℚ⁺.+-assoc q (s ℚ⁺./2) (s ℚ⁺./2) ⟩
       q ℚ⁺.+ (s ℚ⁺./2 ℚ⁺.+ s ℚ⁺./2)
         ≈⟨ ℚ⁺.+-congʳ q ℚ⁺.half+half ⟩
       q ℚ⁺.+ s
     ∎) ,
     x-q₃ ,
     λ s₁ → q₄ , q₂ , ℚ⁺.+-increasing , y-q₄ , z-q₂
   where open ℚ⁺.≤-Reasoning

open interchange (record
                    { isCommutativeSemigroup = record { isSemigroup = record { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = +-cong } ; assoc = +-assoc } ; comm = +-comm } }) public

rational-0 : rational 0ℚ ≤ 0ℝ
rational-0 .*≤* {q} tt = ℚ⁺.fog-nonneg {q}

rational-+ : ∀ q r → 0ℚ ℚ.≤ q → 0ℚ ℚ.≤ r → (rational q + rational r) ≃ rational (q ℚ.+ r)
rational-+ q r 0≤q 0≤r .proj₁ .*≤* {ε} q+r≤ε s =
  qpos.nn+pos q (s /2) 0≤q ,
  qpos.nn+pos r (s /2) 0≤r ,
  qpos.r≤r (begin
              q ℚ.+ qpos.fog (s /2) ℚ.+ (r ℚ.+ qpos.fog (s /2))
            ≈⟨ ℚ-interchange q (qpos.fog (s /2)) r (qpos.fog (s /2)) ⟩
              (q ℚ.+ r) ℚ.+ (qpos.fog (s /2) ℚ.+ qpos.fog (s /2))
            ≈⟨ ℚ.+-congʳ (q ℚ.+ r) (ℚ.≃-sym (qpos.+-fog (s /2) (s /2))) ⟩
              (q ℚ.+ r) ℚ.+ qpos.fog (s /2 ℚ⁺.+ s /2)
            ≤⟨ ℚ.+-mono-≤ q+r≤ε (qpos.fog-mono (qpos.≤-reflexive (qpos.half+half {s}))) ⟩
              qpos.fog ε ℚ.+ qpos.fog s
            ≈⟨ qpos.+-fog ε s ⟩
              qpos.fog (ε ℚ⁺.+ s)
           ∎) ,
  qpos.q≤nn+pos q (s /2) ,
  qpos.q≤nn+pos r (s /2)
  where open ℚ.≤-Reasoning
rational-+ q r 0≤q 0≤r .proj₂ .*≤* {ε} q+r∋ε =
  rational (q ℚ.+ r) .closed {ε} λ s →
  let ε₁ , ε₂ , ε₁+ε₂≤ε+s , q≤ε₁ , r≤ε₂ = q+r∋ε s in
  begin
    q ℚ.+ r
  ≤⟨ ℚ.+-mono-≤ q≤ε₁ r≤ε₂ ⟩
    qpos.fog ε₁ ℚ.+ qpos.fog ε₂
  ≈⟨ ℚ.≃-sym (qpos.+-fog ε₁ ε₂) ⟩
    qpos.fog (ε₁ ℚ⁺.+ ε₂)
  ≤⟨ qpos.fog-mono ε₁+ε₂≤ε+s ⟩
    qpos.fog (ε qpos.+ s)
  ∎
  where open ℚ.≤-Reasoning

rational⁺-+ : ∀ q r → (rational+ q + rational+ r) ≃ rational+ (q ℚ⁺.+ r)
rational⁺-+ q r =
  begin-equality
    rational+ q + rational+ r
  ≈⟨ ≃-refl ⟩
    rational (ℚ⁺.fog q) + rational (ℚ⁺.fog r)
  ≈⟨ rational-+ (qpos.fog q) (qpos.fog r) (qpos.fog-nonneg {q}) (qpos.fog-nonneg {r}) ⟩
    rational (ℚ⁺.fog q ℚ.+ ℚ⁺.fog r)
  ≈⟨ rational-cong (qpos.+-fog q r) ⟩
    rational+ (q ℚ⁺.+ r)
  ∎
  where open ≤-Reasoning

-- TODO:
-- *-assoc
-- x + ∞ = ∞
-- x * ∞ = ∞

-- FIXME: needs a max operation in qpos.agda
{-
*-distribʳ-+ℝ : _DistributesOverʳ_ _≃_ _*_ _+_
*-distribʳ-+ℝ x y z =
  (λ {q} y*x+z*x-q s →
    let q₁ , q₂ , q₁+q₂≤q+s , y*x-q₁ , z*x-q₂ = y*x+z*x-q s in
    let q₃ , q₄ , q₃*q₄≤q₁+s , y-q₃ , x-q₄ = y*x-q₁ s in
    let q₅ , q₆ , q₅*q₆≤q₂+s , z-q₅ , x-q₆ = z*x-q₂ s in
    q₃ ℚ⁺.+ q₅ , {!q₅ ⊔ q₆!} , {!!} , (λ s₁ → q₃ , q₅ , ℚ⁺.+-increasing , y-q₃ , z-q₅) , {!!}) ,
  {!!}
-}

-- reciprocal?
-- would we have 1/ 0 = ∞ ?
{-
1/ℝ_ : ℝᵘ → ℝᵘ -- bit like negation in a ternary frame?
(1/ℝ x) .contains q = ∀ s → Σ[ q₁ ∈ ℚ⁺ ] (1/ q₁ ≤ q + s × ¬ (x .contains q₁)) -- or q₁ ∉ x?
  -- but this negation is not involutive, so this probably won't work?
  -- if we had the corresponding lower set too, then it might work
(1/ℝ x) .upper = {!!}
(1/ℝ x) .closed = {!!}
-}


scale : ℚ⁺ → ℝᵘ → ℝᵘ
scale r x .contains q = ∀ s → Σ[ q₁ ∈ ℚ⁺ ] (r ℚ⁺.* q₁ ℚ⁺.≤ q ℚ⁺.+ s × x .contains q₁)
scale r x .upper q₁≤q₂ rx-q₁ s =
  let q' , r*q'≤q₁+s , x-q' = rx-q₁ s in
  q' , ℚ⁺.≤-trans r*q'≤q₁+s (ℚ⁺.+-mono-≤ q₁≤q₂ ℚ⁺.≤-refl) , x-q'
scale r x .closed {q} h s =
  let q' , ineq , x-q' = h (s ℚ⁺./2) (s ℚ⁺./2) in
  q' ,
  (begin
    r ℚ⁺.* q'
      ≤⟨ ineq ⟩
    q ℚ⁺.+ s ℚ⁺./2 ℚ⁺.+ s ℚ⁺./2
      ≈⟨ ℚ⁺.+-assoc q (s ℚ⁺./2) (s ℚ⁺./2) ⟩
    q ℚ⁺.+ (s ℚ⁺./2 ℚ⁺.+ s ℚ⁺./2)
      ≈⟨ ℚ⁺.+-congʳ q ℚ⁺.half+half ⟩
    q ℚ⁺.+ s
  ∎) ,
  x-q'
  where open ℚ⁺.≤-Reasoning

scale-mono : ∀ {q₁ q₂ x₁ x₂} → q₁ ℚ⁺.≤ q₂ → x₁ ≤ x₂ → scale q₁ x₁ ≤ scale q₂ x₂
scale-mono q₁≤q₂ x₁≤x₂ .*≤* {q} h s =
  let q' , q₂*q'≤q+s , x₂-q' = h s in
  q' , (ℚ⁺.≤-trans (ℚ⁺.*-mono-≤ q₁≤q₂ (ℚ⁺.≤-refl {q'})) q₂*q'≤q+s) , x₁≤x₂ .*≤* x₂-q'

scale-cong : ∀ {q₁ q₂ x₁ x₂} → q₁ ℚ⁺.≃ q₂ → x₁ ≃ x₂ → scale q₁ x₁ ≃ scale q₂ x₂
scale-cong q₁≃q₂ x₁≃x₂ .proj₁ = scale-mono (qpos.≤-reflexive q₁≃q₂) (≤-reflexive x₁≃x₂)
scale-cong q₁≃q₂ x₁≃x₂ .proj₂ = scale-mono (qpos.≤-reflexive (qpos.≃-sym q₁≃q₂)) (≤-reflexive (≃-sym x₁≃x₂))

scale-0 : ∀ {q} → scale q 0ℝ ≤ 0ℝ
scale-0 {q} .*≤* {q₁} tt s =
  ℚ⁺.1/ q ℚ⁺.* q₁ ,
  (begin
    q ℚ⁺.* (ℚ⁺.1/ q ℚ⁺.* q₁)
      ≈⟨ ℚ⁺.≃-sym (ℚ⁺.*-assoc q _ q₁) ⟩
    (q ℚ⁺.* ℚ⁺.1/ q) ℚ⁺.* q₁
      ≈⟨ ℚ⁺.*-cong (ℚ⁺.*-inverseʳ q) ℚ⁺.≃-refl ⟩
    ℚ⁺.1ℚ⁺ ℚ⁺.* q₁
      ≈⟨ ℚ⁺.*-identityˡ q₁ ⟩
    q₁
      ≤⟨ ℚ⁺.+-increasing ⟩
    q₁ ℚ⁺.+ s
  ∎) ,
  tt
  where open ℚ⁺.≤-Reasoning

scale-+ : ∀ {q x y} → scale q (x + y) ≃ (scale q x + scale q y)
scale-+ {q}{x}{y} .proj₁ .*≤* {ε} qx+qy-ε s =
  let ε₁ , ε₂ , ε₁+ε₂≤ε+s , qx-ε₁ , qy-ε₂ = qx+qy-ε (s /2) in
  let ε₁₁ , qε₁₁≤ε₁+s , x-ε₁₁ = qx-ε₁ (s /2 /2) in
  let ε₂₁ , qε₂₁≤ε₂+s , y-ε₂₁ = qy-ε₂ (s /2 /2) in
  ε₁₁ ℚ⁺.+ ε₂₁ ,
  (begin
    q ℚ⁺.* (ε₁₁ ℚ⁺.+ ε₂₁)
      ≈⟨ qpos.*-distribˡ-+ q ε₁₁ ε₂₁ ⟩
    q ℚ⁺.* ε₁₁ ℚ⁺.+ q ℚ⁺.* ε₂₁
      ≤⟨ qpos.+-mono-≤ qε₁₁≤ε₁+s qε₂₁≤ε₂+s ⟩
    (ε₁ ℚ⁺.+ s /2 /2) ℚ⁺.+ (ε₂ ℚ⁺.+ s /2 /2)
      ≈⟨ ℚ⁺-interchange ε₁ (s /2 /2) ε₂ (s /2 /2) ⟩
    (ε₁ ℚ⁺.+ ε₂) ℚ⁺.+ (s /2 /2 ℚ⁺.+ s /2 /2)
      ≤⟨ qpos.+-mono-≤ ε₁+ε₂≤ε+s (qpos.≤-reflexive ℚ⁺.half+half) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
      ≈⟨ qpos.+-assoc ε _ _ ⟩
    ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
      ≈⟨ qpos.+-congʳ ε ℚ⁺.half+half  ⟩
    ε ℚ⁺.+ s
  ∎) ,
  λ r → ε₁₁ , ε₂₁ , ℚ⁺.+-increasing , x-ε₁₁ , y-ε₂₁
  where open ℚ⁺.≤-Reasoning
scale-+ {q}{x}{y} .proj₂ .*≤* {ε} q⟨x+y⟩-ε s =
  let ε₁ , qε₁≤ε+s , x+y-ε₁ = q⟨x+y⟩-ε (s /2) in
  let ε₁₁ , ε₁₂ , ε₁₁+ε₁₂≤ε₁+s , x-ε₁₁ , y-ε₁₂ = x+y-ε₁ (1/ q ℚ⁺.* s /2) in
  q ℚ⁺.* ε₁₁ ,
  q ℚ⁺.* ε₁₂ ,
  (begin
    (q ℚ⁺.* ε₁₁) ℚ⁺.+ (q ℚ⁺.* ε₁₂)
      ≈⟨ qpos.≃-sym (qpos.*-distribˡ-+ q ε₁₁ ε₁₂) ⟩
    q ℚ⁺.* (ε₁₁ ℚ⁺.+ ε₁₂)
      ≤⟨ qpos.*-mono-≤ (qpos.≤-refl {q}) ε₁₁+ε₁₂≤ε₁+s ⟩
    q ℚ⁺.* (ε₁ ℚ⁺.+ (1/ q ℚ⁺.* s /2))
      ≈⟨ qpos.*-distribˡ-+ q ε₁ (1/ q ℚ⁺.* s /2) ⟩
    (q ℚ⁺.* ε₁) ℚ⁺.+ (q ℚ⁺.* (1/ q ℚ⁺.* s /2))
      ≤⟨ qpos.+-mono-≤ qε₁≤ε+s qpos.≤-refl ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ (q ℚ⁺.* (1/ q ℚ⁺.* s /2))
      ≈⟨ qpos.+-congʳ (ε ℚ⁺.+ s /2) (qpos.≃-sym (qpos.*-assoc q (1/ q) (s /2))) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ ((q ℚ⁺.* 1/ q) ℚ⁺.* s /2)
      ≈⟨ qpos.+-congʳ (ε qpos.+ s /2) (qpos.*-cong (qpos.*-inverseʳ q) qpos.≃-refl) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ (qpos.1ℚ⁺ ℚ⁺.* s /2)
      ≈⟨ qpos.+-congʳ (ε qpos.+ s /2) (qpos.*-identityˡ (s /2)) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
      ≈⟨ qpos.+-assoc ε (s /2) (s /2) ⟩
    ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
      ≈⟨ qpos.+-congʳ ε qpos.half+half ⟩
    ε ℚ⁺.+ s
   ∎) ,
  (λ r → ε₁₁ , ℚ⁺.+-increasing , x-ε₁₁) ,
  (λ r → ε₁₂ , ℚ⁺.+-increasing , y-ε₁₂)
  where open ℚ⁺.≤-Reasoning

+-scale : ∀ {q₁ q₂ x} → (scale q₁ x + scale q₂ x) ≤ scale (q₁ ℚ⁺.+ q₂) x
+-scale {q₁}{q₂} .*≤* {ε} h s =
  let ε₁ , ⟨q₁+q₂⟩ε₁≤ε+s , x-ε₁ = h s in
  q₁ qpos.* ε₁ ,
  q₂ qpos.* ε₁ ,
  (begin
    q₁ qpos.* ε₁ qpos.+ q₂ qpos.* ε₁
      ≈⟨ qpos.≃-sym (qpos.*-distribʳ-+ ε₁ q₁ q₂) ⟩
    (q₁ qpos.+ q₂) qpos.* ε₁
      ≤⟨ ⟨q₁+q₂⟩ε₁≤ε+s ⟩
    ε qpos.+ s
  ∎) ,
  (λ r → ε₁ , qpos.+-increasing , x-ε₁) ,
  (λ r → ε₁ , qpos.+-increasing , x-ε₁)
  where open ℚ⁺.≤-Reasoning

1-scale : ∀ {x} → x ≤ scale qpos.1ℚ⁺ x
1-scale {x} .*≤* h =
  x .closed λ s →
  let q₁ , 1*q₁≤q+s , x-q₁ = h s in
  x .upper (qpos.≤-trans (qpos.≤-reflexive (qpos.≃-sym (qpos.*-identityˡ q₁))) 1*q₁≤q+s)
           x-q₁

*-scale : ∀ {q₁ q₂ x} → scale q₁ (scale q₂ x) ≤ scale (q₁ ℚ⁺.* q₂) x
*-scale {q₁}{q₂} .*≤* {ε} x-q₁q₂ s =
  let ε₁ , q₁q₂ε₁≤ε+s , x-ε₁ = x-q₁q₂ s in
  q₂ qpos.* ε₁ ,
  qpos.≤-trans (qpos.≤-reflexive (qpos.≃-sym (qpos.*-assoc q₁ q₂ ε₁))) q₁q₂ε₁≤ε+s ,
  λ r → ε₁ , qpos.+-increasing , x-ε₁

------------------------------------------------------------------------------
-- truncating subtraction, which is essentially an exponential in this
-- posetal category
--
-- to get the full subtraction, we want to basically encode the Day
-- exponential
_⊖_ : ℝᵘ → ℚ⁺ → ℝᵘ
(x ⊖ r) .contains q = x .contains (q ℚ⁺.+ r)
(x ⊖ r) .upper q₁≤q₂ = x .upper (qpos.+-mono-≤ q₁≤q₂ ℚ⁺.≤-refl)
(x ⊖ r) .closed {q} h =
  x .closed (λ s → x .upper (qpos.≤-reflexive (prove 3 ((a ⊕ b) ⊕ c) ((a ⊕ c) ⊕ b) (q ∷ s ∷ r ∷ []))) (h s))
  where open import CommutativeSemigroupSolver (ℚ⁺.+-commutativeSemigroup)
        a = v# 0; b = v# 1; c = v# 2

⊖-iso1 : ∀ {x q y} → (x ⊖ q) ≤ y → x ≤ (y + rational+ q)
⊖-iso1 {x}{q}{y} x⊖q≤y .*≤* {ε} h =
  x .closed λ s →
  let ε₁ , ε₂ , ε₁+ε₂≤ε+s , y-ε₁ , q≤ε₂ = h s in
  x .upper ε₁+ε₂≤ε+s (x .upper (qpos.+-mono-≤ qpos.≤-refl (qpos.r≤r q≤ε₂)) (x⊖q≤y .*≤* y-ε₁))

⊖-iso2 : ∀ {x q y} → x ≤ (y + rational+ q) → (x ⊖ q) ≤ y
⊖-iso2 {x}{q}{y} x≤y+q .*≤* {ε} y-ε =
  x≤y+q .*≤* (λ s → ε , q , ℚ⁺.+-increasing , y-ε , ℚ.≤-refl)

⊖-eval : ∀ {x q} → x ≤ ((x ⊖ q) + rational+ q)
⊖-eval {x}{q} = ⊖-iso1 ≤-refl

⊖-mono : ∀ {x y q₁ q₂} → x ≤ y → q₂ ℚ⁺.≤ q₁ → (x ⊖ q₁) ≤ (y ⊖ q₂)
⊖-mono {x} x≤y q₂≤q₁ .*≤* y-q+q₂ = x .upper (ℚ⁺.+-mono-≤ ℚ⁺.≤-refl q₂≤q₁) (x≤y .*≤* y-q+q₂)

⊖-0 : ∀ r → (rational+ r ⊖ r) ≤ 0ℝ
⊖-0 r .*≤* {q} tt =
   qpos.fog-mono {r} {q ℚ⁺.+ r} (qpos.≤-trans ℚ⁺.+-increasing (qpos.≤-reflexive (ℚ⁺.+-comm r q)))

⊖-≤ : ∀ {x ε} → (x ⊖ ε) ≤ x
⊖-≤ {x} .*≤* = x .upper ℚ⁺.+-increasing

-- FIXME: this is the same proof twice
-- FIXME: in the light of the above observation that ⊖ is a Day exponential, this is currying
⊖-+ : ∀ {x q r} → ((x ⊖ q) ⊖ r) ≃ (x ⊖ (q ℚ⁺.+ r))
⊖-+ {x}{q}{r} .proj₁ .*≤* {ε} =
   x .upper (qpos.≤-reflexive (qpos.≃-trans (qpos.+-congʳ ε (qpos.+-comm q r)) (qpos.≃-sym (qpos.+-assoc ε r q))))
⊖-+ {x}{q}{r} .proj₂ .*≤* {ε} =
   x .upper (qpos.≤-reflexive (qpos.≃-trans (qpos.+-assoc ε r q) (qpos.+-congʳ ε (qpos.+-comm r q))))

-- FIXME: deduce this from the exponential isomorphisms
⊖-+-+ : ∀ {x y q r} → ((x + y) ⊖ (q qpos.+ r)) ≤ ((x ⊖ q) + (y ⊖ r))
⊖-+-+ {x}{y}{q}{r} .*≤* {ε} h s =
  let ε₁ , ε₂ , ε₁+ε₂≤ε+s , x-ε₁ , y-ε₂ = h s in
  ε₁ ℚ⁺.+ q , ε₂ ℚ⁺.+ r ,
  (begin
    (ε₁ ℚ⁺.+ q) ℚ⁺.+ (ε₂ ℚ⁺.+ r)
      ≈⟨ ℚ⁺-interchange ε₁ q ε₂ r ⟩
    (ε₁ ℚ⁺.+ ε₂) ℚ⁺.+ (q ℚ⁺.+ r)
      ≤⟨ qpos.+-mono-≤ ε₁+ε₂≤ε+s qpos.≤-refl ⟩
    (ε ℚ⁺.+ s) ℚ⁺.+ (q ℚ⁺.+ r)
      ≈⟨ qpos.+-assoc ε s (q ℚ⁺.+ r) ⟩
    ε ℚ⁺.+ (s ℚ⁺.+ (q ℚ⁺.+ r))
      ≈⟨ qpos.+-congʳ ε (qpos.+-comm s (q ℚ⁺.+ r)) ⟩
    ε ℚ⁺.+ ((q ℚ⁺.+ r) ℚ⁺.+ s)
      ≈⟨ qpos.≃-sym (qpos.+-assoc ε (q ℚ⁺.+ r) s) ⟩
    ε ℚ⁺.+ (q ℚ⁺.+ r) ℚ⁺.+ s
  ∎) ,
  x-ε₁ , y-ε₂
  where open qpos.≤-Reasoning



-- is this provable some other way? see below: the approximate function
closedness : ∀ {x y} → (∀ ε → (y ⊖ ε) ≤ x) → y ≤ x
closedness {x}{y} h .*≤* x-q = y .closed (λ r → h r .*≤* x-q)

-- or : (∀ ε → y ≤ x + ε) → y ≤ x

------------------------------------------------------------------------------
-- maximum
_⊔_ : ℝᵘ → ℝᵘ → ℝᵘ
(x ⊔ y) .contains q = x .contains q × y .contains q
(x ⊔ y) .upper q₁≤q₂ (x-q₁ , y-q₁) =
  x .upper q₁≤q₂ x-q₁ ,
  y .upper q₁≤q₂ y-q₁
(x ⊔ y) .closed h =
  x .closed (λ r → h r .proj₁) ,
  y .closed (λ r → h r .proj₂)

⊔-upper-1 : ∀ {x y} → x ≤ (x ⊔ y)
⊔-upper-1 .*≤* = proj₁

⊔-upper-2 : ∀ {x y} → y ≤ (x ⊔ y)
⊔-upper-2 .*≤* = proj₂

⊔-least : ∀ {x y z} → x ≤ z → y ≤ z → (x ⊔ y) ≤ z
⊔-least x≤z y≤z .*≤* z-q = x≤z .*≤* z-q , y≤z .*≤* z-q

------------------------------------------------------------------------------
-- minimum
_⊓_ : ℝᵘ → ℝᵘ → ℝᵘ
(x ⊓ y) .contains q = ∀ s → x .contains (q ℚ⁺.+ s) ⊎ y .contains (q ℚ⁺.+ s)
(x ⊓ y) .upper q₁≤q₂ v s =
  [ (λ x-q₁+s → inj₁ (x .upper (qpos.+-mono-≤ q₁≤q₂ qpos.≤-refl) x-q₁+s)) , (λ y-q₁+s → inj₂ (y .upper (qpos.+-mono-≤ q₁≤q₂ qpos.≤-refl) y-q₁+s)) ] (v s)
(x ⊓ y) .closed h s with h (s /2) (s /2)
... | inj₁ p = inj₁ (x .upper (qpos.≤-reflexive (qpos.≃-trans (qpos.+-assoc _ _ _) (qpos.+-congʳ _ (qpos.half+half {s})))) p)
... | inj₂ p = inj₂ (y .upper (qpos.≤-reflexive (qpos.≃-trans (qpos.+-assoc _ _ _) (qpos.+-congʳ _ (qpos.half+half {s})))) p)

⊓-lower-1 : ∀ {x y} → (x ⊓ y) ≤ x
⊓-lower-1 {x}{y} .*≤* x-q s = inj₁ (x .upper qpos.+-increasing x-q)

⊓-lower-2 : ∀ {x y} → (x ⊓ y) ≤ y
⊓-lower-2 {x}{y} .*≤* y-q s = inj₂ (y .upper qpos.+-increasing y-q)

⊓-greatest : ∀ {x y z} → x ≤ y → x ≤ z → x ≤ (y ⊓ z)
⊓-greatest {x} x≤y x≤z .*≤* y⊓z-q = x .closed λ s → [ x≤y .*≤* , x≤z .*≤* ] (y⊓z-q s)

-- FIXME: I guess min and max distribute?

------------------------------------------------------------------------------
-- general suprema
sup : (I : Set) → (I → ℝᵘ) → ℝᵘ
sup I S .contains q = ∀ i → S i .contains q
sup I S .upper q≤r contains-q = λ i → S i .upper q≤r (contains-q i)
sup I S .closed h = λ i → S i .closed λ r → h r i

sup-upper : ∀ {I S} → ∀ i → S i ≤ sup I S
sup-upper i .*≤* q∈sup = q∈sup i

sup-least : ∀ {I S x} → (∀ i → S i ≤ x) → sup I S ≤ x
sup-least h .*≤* q∈x i = h i .*≤* q∈x

sup-mono-≤ : ∀ {I J S₁ S₂} → (f : I → J) → (∀ i → S₁ i ≤ S₂ (f i)) → sup I S₁ ≤ sup J S₂
sup-mono-≤ f S₁≤S₂ = sup-least λ i → ≤-trans (S₁≤S₂ i) (sup-upper (f i))

sup-+ : ∀ {I J} {S₁ : I → ℝᵘ} {S₂ : J → ℝᵘ} → sup (I × J) (λ ij → S₁ (proj₁ ij) + S₂ (proj₂ ij)) ≤ (sup I S₁ + sup J S₂)
sup-+ = sup-least λ i → +-mono-≤ (sup-upper _) (sup-upper _)

approximate : ∀ y → y ≤ sup ℚ⁺ (λ ε → y ⊖ ε)
approximate y .*≤* h = y .closed h
-- FIXME: closedness is now a consequence of this

------------------------------------------------------------------------------
-- infima

inf : (I : Set) → (I → ℝᵘ) → ℝᵘ
inf I S .contains q = ∀ s → Σ[ i ∈ I ] (S i .contains (q qpos.+ s))
inf I S .upper q≤r contains-q s =
  let i , p = contains-q s in
  i , S i .upper (qpos.+-mono-≤ q≤r qpos.≤-refl) p
inf I S .closed {ε} h s =
  let i , p = h (s /2) (s /2) in
  i , S i .upper (qpos.≤-reflexive (qpos.≃-trans (qpos.+-assoc ε (s /2) (s /2)) (qpos.+-congʳ ε qpos.half+half))) p

inf-lower : ∀ {I S} i → inf I S ≤ S i
inf-lower {I}{S} i .*≤* {ε} Si∋ε s = i , S i .upper qpos.+-increasing Si∋ε

inf-greatest : ∀ {I S x} → (∀ i → x ≤ S i) → x ≤ inf I S
inf-greatest {I}{S}{x} h .*≤* {ε} infIS∋ε =
  x .closed λ s →
  let i , Si∋ε+s = infIS∋ε s in
  h i .*≤* Si∋ε+s

------------------------------------------------------------------------------
{-
sqrt : ℝᵘ → ℝᵘ
sqrt x .contains q = x .contains (q qpos.* q)
sqrt x .upper = {!!}
sqrt x .closed h = x .closed (λ s → x .upper {!!} {!!})

sqrt-correct : ∀ x → (sqrt x * sqrt x) ≃ x
sqrt-correct x .proj₁ .*≤* {q} x-q s = {!!} -- need to compute rational square root to within 's' !!!
sqrt-correct x .proj₂ .*≤* sxsx-q = x .closed λ r →
  let q₁ , q₂ , q₁*q₂≤q+s , x-q₁q₁ , x-q₂q₂ = sxsx-q r in
  -- work out which one of q₁ or q₂ is greater
  {!!}
-}
