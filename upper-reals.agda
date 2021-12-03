{-# OPTIONS --without-K --safe #-}

module upper-reals where

open import Level using (0ℓ; suc)
open import Algebra using (CommutativeSemigroup; Commutative; Congruent₂; LeftIdentity; RightIdentity; Associative; LeftZero)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥)
open import Data.Rational.Unnormalised as ℚ using () renaming (ℚᵘ to ℚ; 0ℚᵘ to 0ℚ; 1ℚᵘ to 1ℚ)
import Data.Rational.Unnormalised.Properties as ℚ
open import Relation.Nullary using (yes; no; ¬_)
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

open interchange (ℚ⁺.+-commutativeSemigroup) renaming (interchange to ℚ⁺-interchange) public
open interchange (record
                    { isCommutativeSemigroup = record { isSemigroup = ℚ.+-isSemigroup ; comm = ℚ.+-comm } }) renaming (interchange to ℚ-interchange) public

-- an upper real is a set of upper bounds on a real number
record ℝᵘ : Set₁ where
  no-eta-equality -- FIXME: this seems to speed things up considerably, and makes goals easier to read
  field
    contains : ℚ⁺ → Set
    upper    : ∀ {q₁ q₂} → q₁ ℚ⁺.≤ q₂ → contains q₁ → contains q₂
    closed   : ∀ {q} → (∀ r → contains (q ℚ⁺.+ r)) → contains q -- FIXME: work out what this is really doing. It seems to be some kind of Archimedian principle (no infinitesimals below every element)
  -- FIXME: do we need locatedness? what would this mean?
open ℝᵘ

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

rational-mono-reflect : ∀ {q r} → rational q ≤ rational+ r → q ℚ.≤ ℚ⁺.fog r
rational-mono-reflect {q}{r} q≤r = q≤r .*≤* {r} ℚ.≤-refl

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

rational-0 : rational 0ℚ ≃ 0ℝ
rational-0 .proj₁ .*≤* {q} tt = ℚ⁺.fog-nonneg q
rational-0 .proj₂ = 0-least _

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

rational⁺-* : ∀ q r → (rational+ q * rational+ r) ≃ rational+ (q ℚ⁺.* r)
rational⁺-* q r .proj₁ .*≤* {ε} qr≤ε s =
  q ,
  r ,
  (begin
    q qpos.* r
  ≤⟨ qpos.r≤r qr≤ε ⟩
    ε
  ≤⟨ qpos.+-increasing ⟩
    ε qpos.+ s
  ∎) ,
  ℚ.≤-refl ,
  ℚ.≤-refl
  where open ℚ⁺.≤-Reasoning
rational⁺-* q r .proj₂ .*≤* {ε} qr∋ε =
  rational+ (q ℚ⁺.* r) .closed {ε} λ s →
  let ε₁ , ε₂ , ε₁ε₂≤ε+s , q≤ε₁ , r≤ε₂ = qr∋ε s in
  begin
    qpos.fog q ℚ.* qpos.fog r
  ≤⟨ ℚ.*-monoʳ-≤-pos {qpos.fog q} (ℚ.positive (qpos.fog-positive q)) r≤ε₂ ⟩
    qpos.fog q ℚ.* qpos.fog ε₂
  ≤⟨ ℚ.*-monoˡ-≤-pos (ℚ.positive (qpos.fog-positive ε₂)) q≤ε₁ ⟩
    qpos.fog ε₁ ℚ.* qpos.fog ε₂
  ≈⟨ ℚ.≃-sym (qpos.*-fog ε₁ ε₂) ⟩
    qpos.fog (ε₁ ℚ⁺.* ε₂)
  ≤⟨ qpos.fog-mono ε₁ε₂≤ε+s ⟩
    qpos.fog (ε ℚ⁺.+ s)
  ∎
  where open ℚ.≤-Reasoning

rational⁺-+ : ∀ q r → (rational+ q + rational+ r) ≃ rational+ (q ℚ⁺.+ r)
rational⁺-+ q r =
  begin-equality
    rational+ q + rational+ r
  ≈⟨ ≃-refl ⟩
    rational (ℚ⁺.fog q) + rational (ℚ⁺.fog r)
  ≈⟨ rational-+ (qpos.fog q) (qpos.fog r) (qpos.fog-nonneg q) (qpos.fog-nonneg r) ⟩
    rational (ℚ⁺.fog q ℚ.+ ℚ⁺.fog r)
  ≈⟨ rational-cong (qpos.+-fog q r) ⟩
    rational+ (q ℚ⁺.+ r)
  ∎
  where open ≤-Reasoning

rational+<∞ : ∀ q → rational+ q < ∞
rational+<∞ q = q , ℚ.≤-refl , (λ x → x)

module _ where
  open import Data.Integer
  open import Data.Nat

  0≤1 : 0ℚ ℚ.≤ 1ℚ
  0≤1 = ℚ.*≤* (+≤+ z≤n)

rational<∞ : ∀ q → rational q < ∞
rational<∞ q with ℚ.<-cmp 0ℚ q
... | Relation.Binary.tri< a ¬b ¬c = rational+<∞ qpos.⟨ q , (ℚ.positive a) ⟩
... | Relation.Binary.tri≈ ¬a b ¬c = ℚ⁺.1ℚ⁺ , ℚ.≤-trans (ℚ.≤-reflexive (ℚ.≃-sym b)) 0≤1 , λ x → x
... | Relation.Binary.tri> ¬a ¬b c = ℚ⁺.1ℚ⁺ , ℚ.<⇒≤ (ℚ.<-≤-trans c 0≤1) , λ x → x

*-zeroʳ : ∀ x → x < ∞ → (x * 0ℝ) ≃ 0ℝ
*-zeroʳ x (ε₁ , x∋ε₁ , _) .proj₁ .*≤* {ε} tt s =
  ε₁ ,
  1/ ε₁ qpos.* (ε qpos.+ s) ,
  (begin
    ε₁ ℚ⁺.* (1/ ε₁ qpos.* (ε qpos.+ s))
  ≈⟨ qpos.≃-sym (qpos.*-assoc ε₁ (1/ ε₁) (ε qpos.+ s)) ⟩
    (ε₁ ℚ⁺.* 1/ ε₁) qpos.* (ε qpos.+ s)
  ≈⟨ qpos.*-cong (qpos.*-inverseʳ ε₁) qpos.≃-refl ⟩
    qpos.1ℚ⁺ qpos.* (ε qpos.+ s)
  ≈⟨ qpos.*-identityˡ (ε qpos.+ s) ⟩
    ε ℚ⁺.+ s
  ∎) ,
  x∋ε₁ ,
  tt
  where open ℚ⁺.≤-Reasoning
*-zeroʳ x x<∞ .proj₂ = 0-least (x * 0ℝ)

*-zeroˡ : ∀ x → x < ∞ → (0ℝ * x) ≃ 0ℝ
*-zeroˡ x x<∞ = ≃-trans (*-comm 0ℝ x) (*-zeroʳ x x<∞)

rational-* : ∀ q r → 0ℚ ℚ.≤ q → 0ℚ ℚ.≤ r → (rational q * rational r) ≃ rational (q ℚ.* r)
rational-* q r 0≤q 0≤r with ℚ.<-cmp 0ℚ q
... | Relation.Binary.tri≈ _ q≃0 _ =
  begin-equality
    rational q * rational r
  ≈⟨ *-cong (rational-cong (ℚ.≃-sym q≃0)) ≃-refl ⟩
    rational 0ℚ * rational r
  ≈⟨ *-cong rational-0 ≃-refl ⟩
    0ℝ * rational r
  ≈⟨ *-zeroˡ (rational r) (rational<∞ r) ⟩
    0ℝ
  ≈⟨ ≃-sym rational-0 ⟩
    rational 0ℚ
  ≈⟨ rational-cong (ℚ.≃-sym (ℚ.*-zeroˡ r)) ⟩
    rational (0ℚ ℚ.* r)
  ≈⟨ rational-cong (ℚ.*-cong q≃0 (ℚ.≃-refl {r})) ⟩
    rational (q ℚ.* r)
  ∎
  where open ≤-Reasoning
... | Relation.Binary.tri> _ _ q<0 = Data.Empty.⊥-elim (ℚ.<⇒≱ q<0 0≤q)
... | Relation.Binary.tri< 0<q _ _ with ℚ.<-cmp 0ℚ r
... | Relation.Binary.tri≈ _ r≃0 _ =
  begin-equality
    rational q * rational r
  ≈⟨ *-cong ≃-refl (rational-cong (ℚ.≃-sym r≃0)) ⟩
    rational q * rational 0ℚ
  ≈⟨ *-cong ≃-refl rational-0 ⟩
    rational q * 0ℝ
  ≈⟨ *-zeroʳ (rational q) (rational<∞ q) ⟩
    0ℝ
  ≈⟨ ≃-sym rational-0 ⟩
    rational 0ℚ
  ≈⟨ rational-cong (ℚ.≃-sym (ℚ.*-zeroʳ q)) ⟩
    rational (q ℚ.* 0ℚ)
  ≈⟨ rational-cong (ℚ.*-cong (ℚ.≃-refl {q}) r≃0) ⟩
    rational (q ℚ.* r)
  ∎
  where open ≤-Reasoning
... | Relation.Binary.tri> _ _ r<0 = Data.Empty.⊥-elim (ℚ.<⇒≱ r<0 0≤r)
... | Relation.Binary.tri< 0<r _ _ =
  begin-equality
    (rational q * rational r)
  ≈⟨ rational⁺-* qpos.⟨ q , ℚ.positive 0<q ⟩ qpos.⟨ r , ℚ.positive 0<r ⟩ ⟩
    rational (q ℚ.* r)
  ∎
  where open ≤-Reasoning

*-infinityʳ : ∀ x → (x * ∞) ≃ ∞
*-infinityʳ x .proj₁ = ∞-greatest _
*-infinityʳ x .proj₂ .*≤* {ε} x∞∋ε =
  let _ , _ , _ , _ , ϕ = x∞∋ε ℚ⁺.1ℚ⁺ in
  ϕ

+-infinityʳ : ∀ x → (x + ∞) ≃ ∞
+-infinityʳ x .proj₁ = ∞-greatest _
+-infinityʳ x .proj₂ .*≤* {ε} x+∞∋ε =
  let _ , _ , _ , _ , ϕ = x+∞∋ε ℚ⁺.1ℚ⁺ in
  ϕ

1ℝ : ℝᵘ
1ℝ = rational 1ℚ

*-identityˡ : ∀ x → (1ℝ * x) ≃ x
*-identityˡ x .proj₁ .*≤* {ε} x∋ε s =
  ℚ⁺.1ℚ⁺ ,
  ε ,
  qpos.≤-trans (qpos.≤-reflexive (qpos.*-identityˡ ε)) qpos.+-increasing ,
  ℚ.≤-refl ,
  x∋ε
*-identityˡ x .proj₂ .*≤* {ε} 1x∋ε =
  x .closed λ s →
  let ε₁ , ε₂ , ε₁ε₂≤ε+s , 1≤ε₁ , x∋ε₂ = 1x∋ε s in
  x .upper
    (begin
      ε₂
    ≈⟨ qpos.≃-sym (qpos.*-identityˡ ε₂) ⟩
      ℚ⁺.1ℚ⁺ ℚ⁺.* ε₂
    ≤⟨ qpos.*-mono-≤ (qpos.r≤r 1≤ε₁) (qpos.≤-refl {ε₂}) ⟩
      ε₁ ℚ⁺.* ε₂
    ≤⟨ ε₁ε₂≤ε+s ⟩
      ε ℚ⁺.+ s
    ∎)
    x∋ε₂
    where open ℚ⁺.≤-Reasoning

*-identityʳ : ∀ x → (x * 1ℝ) ≃ x
*-identityʳ x = ≃-trans (*-comm x 1ℝ) (*-identityˡ x)

*-assoc : Associative _≃_ _*_
*-assoc x y z .proj₁ .*≤* {ε} x[yz]∋ε s =
  let ε₁ , ε₂ , ε₁ε₂≤ε+s , x∋ε₁ , yz∋ε₂ = x[yz]∋ε (s /2) in
  let ε₂₁ , ε₂₂ , ε₂₁ε₂₂≤ε₂+s , y∋ε₂₁ , z∋ε₂₂ = yz∋ε₂ (1/ ε₁ ℚ⁺.* s /2) in
  ε₁ ℚ⁺.* ε₂₁ ,
  ε₂₂ ,
  (begin
    (ε₁ ℚ⁺.* ε₂₁) ℚ⁺.* ε₂₂
  ≈⟨ ℚ⁺.*-assoc ε₁ ε₂₁ ε₂₂ ⟩
    ε₁ ℚ⁺.* (ε₂₁ ℚ⁺.* ε₂₂)
  ≤⟨ qpos.*-mono-≤ (ℚ⁺.≤-refl {ε₁}) ε₂₁ε₂₂≤ε₂+s ⟩
    ε₁ ℚ⁺.* (ε₂ ℚ⁺.+ (1/ ε₁ ℚ⁺.* s /2))
  ≈⟨ qpos.*-distribˡ-+ ε₁ ε₂ (1/ ε₁ ℚ⁺.* s /2) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ ε₁ ℚ⁺.* (1/ ε₁ ℚ⁺.* s /2)
  ≈⟨ qpos.+-congʳ (ε₁ ℚ⁺.* ε₂) (qpos.≃-sym (qpos.*-assoc ε₁ (1/ ε₁) (s /2))) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ (ε₁ ℚ⁺.* 1/ ε₁) ℚ⁺.* s /2
  ≈⟨ qpos.+-congʳ (ε₁ ℚ⁺.* ε₂) (qpos.*-congˡ (s /2) (qpos.*-inverseʳ ε₁)) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ ℚ⁺.1ℚ⁺ ℚ⁺.* s /2
  ≈⟨ qpos.+-congʳ (ε₁ ℚ⁺.* ε₂) (qpos.*-identityˡ (s /2)) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ s /2
  ≤⟨ qpos.+-mono-≤ ε₁ε₂≤ε+s (ℚ⁺.≤-refl {s /2}) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
  ≈⟨ ℚ⁺.+-assoc ε (s /2) (s /2) ⟩
    ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
  ≈⟨ ℚ⁺.+-congʳ ε qpos.half+half ⟩
    ε ℚ⁺.+ s
  ∎) ,
  (λ r → ε₁ , ε₂₁ , ℚ⁺.+-increasing , x∋ε₁ , y∋ε₂₁) ,
  z∋ε₂₂
  where open ℚ⁺.≤-Reasoning
*-assoc x y z .proj₂ .*≤* {ε} [xy]z∋ε s =
  let ε₁ , ε₂ , ε₁ε₂≤ε+ , xy∋ε₁ , z∋ε₂ = [xy]z∋ε (s /2) in
  let ε₁₁ , ε₁₂ , ε₁₁ε₁₂≤ε₁+ , x∋ε₁₁ , y∋ε₁₂ = xy∋ε₁ (s /2 ℚ⁺.* 1/ ε₂) in
  ε₁₁ ,
  ε₁₂ ℚ⁺.* ε₂ ,
  (begin
    ε₁₁ ℚ⁺.* (ε₁₂ ℚ⁺.* ε₂)
  ≈⟨ qpos.≃-sym (qpos.*-assoc ε₁₁ ε₁₂ ε₂) ⟩
    (ε₁₁ ℚ⁺.* ε₁₂) ℚ⁺.* ε₂
  ≤⟨ qpos.*-mono-≤ ε₁₁ε₁₂≤ε₁+ (ℚ⁺.≤-refl {ε₂}) ⟩
    (ε₁ ℚ⁺.+ (s /2 ℚ⁺.* 1/ ε₂)) ℚ⁺.* ε₂
  ≈⟨ qpos.*-distribʳ-+ ε₂ ε₁ (s /2 ℚ⁺.* 1/ ε₂) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ (s /2 ℚ⁺.* 1/ ε₂) ℚ⁺.* ε₂
  ≈⟨ qpos.+-congʳ (ε₁ ℚ⁺.* ε₂) (qpos.*-assoc (s /2) (1/ ε₂) ε₂) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ s /2 ℚ⁺.* (1/ ε₂ ℚ⁺.* ε₂)
  ≈⟨ qpos.+-congʳ (ε₁ ℚ⁺.* ε₂) (qpos.*-congʳ (s /2) (qpos.*-inverseˡ ε₂)) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ s /2 ℚ⁺.* ℚ⁺.1ℚ⁺
  ≈⟨ qpos.+-congʳ (ε₁ ℚ⁺.* ε₂) (qpos.*-identityʳ (s /2)) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ s /2
  ≤⟨ qpos.+-mono-≤ ε₁ε₂≤ε+ (ℚ⁺.≤-refl {s /2}) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
  ≈⟨ ℚ⁺.+-assoc ε (s /2) (s /2) ⟩
    ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
  ≈⟨ ℚ⁺.+-congʳ ε qpos.half+half ⟩
    ε ℚ⁺.+ s
  ∎) ,
  x∋ε₁₁ ,
  λ r → ε₁₂ , ε₂ , ℚ⁺.+-increasing , y∋ε₁₂ , z∋ε₂
  where open ℚ⁺.≤-Reasoning

*-distribʳ-+ : ∀ x y z → ((y + z) * x) ≃ ((y * x) + (z * x))
*-distribʳ-+ x y z .proj₁ .*≤* {ε} yx+zx∋ε s =
  let ε₁ , ε₂ , ε₁+ε₂≤ε+ , yx∋ε₁ , zx∋ε₂ = yx+zx∋ε (s /2) in
  let ε₁₁ , ε₁₂ , ε₁₁ε₁₂≤ε₁+ , y∋ε₁₁ , x∋ε₁₂ = yx∋ε₁ (s /2 /2) in
  let ε₂₁ , ε₂₂ , ε₂₁ε₂₂≤ε₂+ , z∋ε₂₁ , x∋ε₂₂ = zx∋ε₂ (s /2 /2) in
  ε₁₁ ℚ⁺.+ ε₂₁ ,
  ε₁₂ ℚ⁺.⊓ ε₂₂ ,
  (begin
    (ε₁₁ ℚ⁺.+ ε₂₁) ℚ⁺.* (ε₁₂ ℚ⁺.⊓ ε₂₂)
  ≈⟨ ℚ⁺.*-distribʳ-+ (ε₁₂ ℚ⁺.⊓ ε₂₂) ε₁₁ ε₂₁ ⟩
    ε₁₁ ℚ⁺.* (ε₁₂ ℚ⁺.⊓ ε₂₂) ℚ⁺.+ ε₂₁ ℚ⁺.* (ε₁₂ ℚ⁺.⊓ ε₂₂)
  ≤⟨ qpos.+-mono-≤ (qpos.*-mono-≤ (qpos.≤-refl {ε₁₁}) (qpos.⊓-lower-1 ε₁₂ ε₂₂)) (qpos.*-mono-≤ (qpos.≤-refl {ε₂₁}) (qpos.⊓-lower-2 ε₁₂ ε₂₂)) ⟩
    ε₁₁ ℚ⁺.* ε₁₂ ℚ⁺.+ ε₂₁ ℚ⁺.* ε₂₂
  ≤⟨ qpos.+-mono-≤ ε₁₁ε₁₂≤ε₁+ ε₂₁ε₂₂≤ε₂+ ⟩
    (ε₁ ℚ⁺.+ s /2 /2) ℚ⁺.+ (ε₂ ℚ⁺.+ s /2 /2)
  ≈⟨ ℚ⁺-interchange ε₁ (s /2 /2) ε₂ (s /2 /2) ⟩
    (ε₁ ℚ⁺.+ ε₂) ℚ⁺.+ (s /2 /2 ℚ⁺.+ s /2 /2)
  ≈⟨ qpos.+-congʳ (ε₁ ℚ⁺.+ ε₂) (qpos.half+half {s /2}) ⟩
    (ε₁ ℚ⁺.+ ε₂) ℚ⁺.+ s /2
  ≤⟨ qpos.+-mono-≤ ε₁+ε₂≤ε+ (qpos.≤-refl {s /2}) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
  ≈⟨ qpos.+-assoc ε (s /2) (s /2) ⟩
    ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
  ≈⟨ qpos.+-congʳ ε (qpos.half+half {s}) ⟩
    ε ℚ⁺.+ s
  ∎) ,
  (λ r → ε₁₁ , ε₂₁ , ℚ⁺.+-increasing , y∋ε₁₁ , z∋ε₂₁) ,
  x∋⊓ ε₁₂ ε₂₂ x∋ε₁₂ x∋ε₂₂
  where open ℚ⁺.≤-Reasoning
        x∋⊓ : ∀ ε₁ ε₂ → x .contains ε₁ → x .contains ε₂ → x .contains (ε₁ ℚ⁺.⊓ ε₂)
        x∋⊓ ε₁ ε₂ x∋ε₁ x∋ε₂ with qpos.⊓-selective ε₁ ε₂
        x∋⊓ ε₁ ε₂ x∋ε₁ x∋ε₂ | inj₁ p = x .upper (qpos.≤-reflexive (qpos.≃-sym p)) x∋ε₁
        x∋⊓ ε₁ ε₂ x∋ε₁ x∋ε₂ | inj₂ p = x .upper (qpos.≤-reflexive (qpos.≃-sym p)) x∋ε₂
*-distribʳ-+ x y z .proj₂ .*≤* {ε} [y+z]x∋ε s =
  let ε₁ , ε₂ , ε₁ε₂≤ε+ , y+z∋ε₁ , x∋ε₂ = [y+z]x∋ε (s /2) in
  let ε₁₁ , ε₁₂ , ε₁₁+ε₁₂≤ε₁+ , y∋ε₁₁ , z∋ε₁₂ = y+z∋ε₁ (s /2 ℚ⁺.* 1/ ε₂) in
  ε₁₁ ℚ⁺.* ε₂ ,
  ε₁₂ ℚ⁺.* ε₂ ,
  (begin
    (ε₁₁ ℚ⁺.* ε₂) ℚ⁺.+ (ε₁₂ ℚ⁺.* ε₂)
  ≈⟨ qpos.≃-sym (qpos.*-distribʳ-+ ε₂ ε₁₁ ε₁₂) ⟩
    (ε₁₁ ℚ⁺.+ ε₁₂) ℚ⁺.* ε₂
  ≤⟨ qpos.*-mono-≤ ε₁₁+ε₁₂≤ε₁+ (qpos.≤-refl {ε₂}) ⟩
    (ε₁ ℚ⁺.+ (s /2 ℚ⁺.* 1/ ε₂)) ℚ⁺.* ε₂
  ≈⟨ qpos.*-distribʳ-+ ε₂ ε₁ (s /2 ℚ⁺.* 1/ ε₂) ⟩
    (ε₁ ℚ⁺.* ε₂) ℚ⁺.+ (s /2 ℚ⁺.* 1/ ε₂) ℚ⁺.* ε₂
  ≈⟨ qpos.+-congʳ (ε₁ ℚ⁺.* ε₂) (qpos.*-assoc (s /2) (1/ ε₂) ε₂) ⟩
    (ε₁ ℚ⁺.* ε₂) ℚ⁺.+ s /2 ℚ⁺.* (1/ ε₂ ℚ⁺.* ε₂)
  ≈⟨ qpos.+-congʳ (ε₁ ℚ⁺.* ε₂) (qpos.*-congʳ (s /2) (qpos.*-inverseˡ ε₂)) ⟩
    (ε₁ ℚ⁺.* ε₂) ℚ⁺.+ s /2 ℚ⁺.* ℚ⁺.1ℚ⁺
  ≈⟨ qpos.+-congʳ (ε₁ ℚ⁺.* ε₂) (qpos.*-identityʳ (s /2)) ⟩
    (ε₁ ℚ⁺.* ε₂) ℚ⁺.+ s /2
  ≤⟨ qpos.+-mono-≤ ε₁ε₂≤ε+ (qpos.≤-refl {s /2}) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
  ≈⟨ qpos.+-assoc ε (s /2) (s /2) ⟩
    ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
  ≈⟨ qpos.+-congʳ ε (qpos.half+half {s}) ⟩
    ε ℚ⁺.+ s
  ∎) ,
  (λ r → ε₁₁ , ε₂ , ℚ⁺.+-increasing , y∋ε₁₁ , x∋ε₂) ,
  (λ r → ε₁₂ , ε₂ , ℚ⁺.+-increasing , z∋ε₁₂ , x∋ε₂)
  where open ℚ⁺.≤-Reasoning

*-distribˡ-+ : ∀ x y z → (x * (y + z)) ≃ ((x * y) + (x * z))
*-distribˡ-+ x y z =
  begin-equality
    x * (y + z)
  ≈⟨ *-comm x (y + z) ⟩
    (y + z) * x
  ≈⟨ *-distribʳ-+ x y z ⟩
    (y * x) + (z * x)
  ≈⟨ +-cong (*-comm y x) (*-comm z x) ⟩
    (x * y) + (x * z)
  ∎
  where open ≤-Reasoning


------------------------------------------------------------------------------
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

------------------------------------------------------------------------------
{-
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

rational-scale : ∀ q₁ q₂ → 0ℚ ℚ.≤ q₂ → rational (ℚ⁺.fog q₁ ℚ.* q₂) ≃ scale q₁ (rational q₂)
rational-scale q₁ q₂ 0≤q₂ .proj₁ .*≤* {ε} [q₁]*q₂≤ε =
  rational (qpos.fog q₁ ℚ.* q₂) .closed {ε} λ s →
  let ε₁ , q₁ε₁≤ε+s , q₂≤ε₁ = [q₁]*q₂≤ε s in
  begin
    qpos.fog q₁ ℚ.* q₂
  ≤⟨ ℚ.*-monoʳ-≤-pos {ℚ⁺.fog q₁} (ℚ.positive (ℚ⁺.fog-positive {q₁})) q₂≤ε₁ ⟩
    qpos.fog q₁ ℚ.* qpos.fog ε₁
  ≈⟨ qpos.*-fog q₁ ε₁ ⟩
    qpos.fog (q₁ ℚ⁺.* ε₁)
  ≤⟨ qpos.fog-mono q₁ε₁≤ε+s ⟩
    qpos.fog (ε qpos.+ s)
  ∎
  where open ℚ.≤-Reasoning
rational-scale q₁ q₂ 0≤q₂ .proj₂ .*≤* {ε} q₁q₂≤ε s =
  qpos.nn+pos q₂ (1/ q₁ ℚ⁺.* s) 0≤q₂ ,
  qpos.r≤r (begin
             qpos.fog q₁ ℚ.* (q₂ ℚ.+ qpos.fog (1/ q₁ ℚ⁺.* s))
           ≈⟨ ℚ.*-distribˡ-+ (qpos.fog q₁) q₂ (qpos.fog (1/ q₁ ℚ⁺.* s)) ⟩
             qpos.fog q₁ ℚ.* q₂ ℚ.+ qpos.fog q₁ ℚ.* qpos.fog (1/ q₁ ℚ⁺.* s)
           ≤⟨ ℚ.+-mono-≤ q₁q₂≤ε (ℚ.≤-refl {qpos.fog q₁ ℚ.* qpos.fog (1/ q₁ ℚ⁺.* s)}) ⟩
             qpos.fog ε ℚ.+ qpos.fog q₁ ℚ.* qpos.fog (1/ q₁ ℚ⁺.* s)
           ≈⟨ ℚ.+-congʳ (qpos.fog ε) (ℚ.≃-sym (qpos.*-fog q₁ (1/ q₁ ℚ⁺.* s))) ⟩
             qpos.fog ε ℚ.+ qpos.fog (q₁ ℚ⁺.* (1/ q₁ ℚ⁺.* s))
           ≈⟨ ℚ.+-congʳ (qpos.fog ε) (qpos.fog-cong (ℚ⁺.≃-sym (ℚ⁺.*-assoc q₁ (1/ q₁) s))) ⟩
             qpos.fog ε ℚ.+ qpos.fog ((q₁ ℚ⁺.* 1/ q₁) ℚ⁺.* s)
           ≈⟨ ℚ.+-congʳ (qpos.fog ε) (qpos.fog-cong (qpos.*-cong (qpos.*-inverseʳ q₁) (qpos.≃-refl {s}))) ⟩
             qpos.fog ε ℚ.+ qpos.fog (ℚ⁺.1ℚ⁺ ℚ⁺.* s)
           ≈⟨ ℚ.+-congʳ (qpos.fog ε) (qpos.fog-cong (qpos.*-identityˡ s)) ⟩
             qpos.fog ε ℚ.+ qpos.fog s
           ∎) ,
  qpos.q≤nn+pos q₂ (1/ q₁ ℚ⁺.* s)
  where open ℚ.≤-Reasoning
-}

------------------------------------------------------------------------------
-- truncating subtraction, which is essentially an exponential
-- ("residual") in the reversed poset.
_⊝_ : ℝᵘ → ℝᵘ → ℝᵘ
(x ⊝ y) .contains ε =
  ∀ ε' → y .contains ε' → x .contains (ε ℚ⁺.+ ε')
(x ⊝ y) .upper ε₁≤ε₂ h ε' y∋ε' =
  x .upper (qpos.+-mono-≤ ε₁≤ε₂ qpos.≤-refl) (h ε' y∋ε')
(x ⊝ y) .closed {ε} h ε' y∋ε' =
  x .closed λ s → x .upper (qpos.≤-reflexive (eq s)) (h s ε' y∋ε')
  where open import CommutativeSemigroupSolver (ℚ⁺.+-commutativeSemigroup)
        a = v# 0; b = v# 1; c = v# 2
        eq : ∀ s → ε qpos.+ s qpos.+ ε' qpos.≃ ε qpos.+ ε' qpos.+ s
        eq s = prove 3 ((a ⊕ b) ⊕ c) ((a ⊕ c) ⊕ b) (ε ∷ s ∷ ε' ∷ [])

residual-1 : ∀ {x y z} → (x ⊝ y) ≤ z → x ≤ (y + z)
residual-1 {x} {y} {z} x⊝y≤z .*≤* {ε} y+z∈ε =
  x .closed λ s →
  let ε₁ , ε₂ , ε₁+ε₂≤ε+s , y∋ε₁ , z∋ε₂ = y+z∈ε s in
  x .upper (ℚ⁺.≤-trans (ℚ⁺.≤-reflexive (ℚ⁺.+-comm ε₂ ε₁)) ε₁+ε₂≤ε+s)
           (x⊝y≤z .*≤* z∋ε₂ ε₁ y∋ε₁)

residual-2 : ∀ {x y z} → x ≤ (y + z) → (x ⊝ y) ≤ z
residual-2 {x} {y} {z} x≤y+z .*≤* {ε} z∋ε ε' y∋ε' =
  x≤y+z .*≤* λ s →
  ε' ,
  ε ,
  qpos.≤-trans (qpos.≤-reflexive (qpos.+-comm ε' ε)) qpos.+-increasing ,
  y∋ε' ,
  z∋ε

{-
⊝-curry : ∀ x y z → ((x ⊝ y) ⊝ z) ≃ (x ⊝ (y + z))
⊝-curry x y z .proj₁ = residual-2 _ _ _ (residual-2 _ _ _ (≤-trans {!!} (≤-reflexive (+-assoc y z (x ⊝ (y + z))))))
⊝-curry x y z .proj₂ = residual-2 {!!} {!!} {!!} {!!}
-}

------------------------------------------------------------------------------
-- FIXME: this is the old truncating subtraction, just for rationals
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

⊖-iso1-0 : ∀ {x q} → (x ⊖ q) ≤ 0ℝ → x ≤ rational+ q
⊖-iso1-0 {x}{q} x⊖q≤0 =
  begin
    x
  ≤⟨ ⊖-iso1 x⊖q≤0 ⟩
    0ℝ + rational+ q
  ≈⟨ +-identityˡ (rational+ q) ⟩
    rational+ q
  ∎
  where open ≤-Reasoning


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

⊖-+-out : ∀ x y ε → ((x + y) ⊖ ε) ≤ ((x ⊖ ε) + y)
⊖-+-out x y ε = ⊖-iso2 (begin
    x + y
  ≤⟨ +-mono-≤ ⊖-eval ≤-refl ⟩
    ((x ⊖ ε) + rational+ ε) + y
  ≈⟨ +-assoc (x ⊖ ε) (rational+ ε) y ⟩
    (x ⊖ ε) + (rational+ ε + y)
  ≈⟨ +-cong ≃-refl (+-comm (rational+ ε) y) ⟩
    (x ⊖ ε) + (y + rational+ ε)
  ≈⟨ ≃-sym (+-assoc (x ⊖ ε) y (rational+ ε)) ⟩
    ((x ⊖ ε) + y) + rational+ ε
  ∎)
  where open ≤-Reasoning


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

-- An archimedian principle: there are no elements infinitesimally below 'y'
approximate : ∀ y → y ≤ sup ℚ⁺ (λ ε → y ⊖ ε)
approximate y .*≤* h = y .closed h
-- FIXME: “closedness” above is now a consequence of this

{- -- this isn't true... cannot approximate numbers from below in this system
sup-approx : ∀ y → y ≃ sup (Σ[ q ∈ ℚ⁺ ] (rational+ q ≤ y)) (λ i → rational+ (i .proj₁))
sup-approx y .proj₁ .*≤* {ε} h = {!!}
sup-approx y .proj₂ = sup-least (λ i → i .proj₂)
-}

sup-0 : sup ⊥ (λ ()) ≃ 0ℝ
sup-0 .proj₁ .*≤* tt ()
sup-0 .proj₂ = 0-least _

{-
-- is there a rational between (y ⊖ ε) and y? how could make sure there is? open sets?
-}

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

-- Another statement of the archimedian principle? But this doesn't
-- use .closed? Maybe that's because it is specialised to 0?
inf-ℚ⁺ : inf ℚ⁺ rational+ ≃ 0ℝ
inf-ℚ⁺ .proj₁ .*≤* {ε} tt s = ε , qpos.fog-mono (ℚ⁺.+-increasing {ε} {s})
inf-ℚ⁺ .proj₂ = 0-least _

inf-empty : inf ⊥ (λ ()) ≃ ∞
inf-empty .proj₁ = ∞-greatest _
inf-empty .proj₂ = inf-greatest (λ ())

inf-+ : ∀ {I₁ I₂ S₁ S₂} →
        inf (I₁ × I₂) (λ i → S₁ (i .proj₁) + S₂ (i .proj₂)) ≃ (inf I₁ S₁ + inf I₂ S₂)
inf-+ {I₁}{I₂}{S₁}{S₂} .proj₁ .*≤* {ε} ⊓₁+⊓₂∋ε s =
  let ε₁ , ε₂ , ε₁+ε₂≤ε+ , ⊓₁∋ε₁ , ⊓₂∋ε₂ = ⊓₁+⊓₂∋ε (s /2) in
  let i₁ , S₁i₁∋ε₁+ = ⊓₁∋ε₁ (s /2 /2) in
  let i₂ , S₂i₂∋ε₂+ = ⊓₂∋ε₂ (s /2 /2) in
  (i₁ , i₂) ,
  λ r → ε₁ ℚ⁺.+ s /2 /2 ,
         ε₂ ℚ⁺.+ s /2 /2 ,
         (begin
           (ε₁ ℚ⁺.+ s /2 /2) ℚ⁺.+ (ε₂ ℚ⁺.+ s /2 /2)
         ≈⟨ ℚ⁺-interchange ε₁ (s /2 /2) ε₂ (s /2 /2) ⟩
           (ε₁ ℚ⁺.+ ε₂) ℚ⁺.+ (s /2 /2 ℚ⁺.+ s /2 /2)
         ≈⟨ ℚ⁺.+-congʳ (ε₁ ℚ⁺.+ ε₂) (ℚ⁺.half+half {s /2}) ⟩
           (ε₁ ℚ⁺.+ ε₂) ℚ⁺.+ s /2
         ≤⟨ qpos.+-mono-≤ ε₁+ε₂≤ε+ (ℚ⁺.≤-refl {s /2}) ⟩
           (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
         ≈⟨ qpos.+-assoc ε (s /2) (s /2) ⟩
           ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
         ≈⟨ qpos.+-congʳ ε (ℚ⁺.half+half {s}) ⟩
           ε ℚ⁺.+ s
         ≤⟨ ℚ⁺.+-increasing ⟩
           ε ℚ⁺.+ s ℚ⁺.+ r
         ∎) ,
         S₁i₁∋ε₁+ ,
         S₂i₂∋ε₂+
  where open ℚ⁺.≤-Reasoning
inf-+ {I₁}{I₂}{S₁}{S₂} .proj₂ =
  inf-greatest (λ i → +-mono-≤ (inf-lower (i .proj₁)) (inf-lower (i .proj₂)))

-- every number can be approximated from above
approx : ∀ y → y ≃ inf (Σ[ q ∈ ℚ⁺ ] (y ≤ rational+ q)) (λ i → rational+ (i .proj₁))
approx y .proj₁ = inf-greatest (λ i → i .proj₂)
approx y .proj₂ .*≤* {ε} y∋ε s =
  (ε , (record { *≤* = λ x → y .upper (qpos.r≤r x) y∋ε })) , qpos.fog-mono (qpos.+-increasing {ε}{s})


as-inf : ∀ x y → (x ⊝ y) ≃ inf (Σ[ q ∈ ℚ⁺ ] (x ≤ (y + rational+ q))) (λ x → rational+ (x .proj₁))
as-inf x y .proj₁ = inf-greatest (λ i → residual-2 (i .proj₂))
as-inf x y .proj₂ =
  ≤-trans
    (inf-greatest (λ i → inf-lower (i .proj₁ , residual-1 (i .proj₂))))
    (≤-reflexive (≃-sym (approx (x ⊝ y))))

------------------------------------------------------------------------------
{-
sqrt : ℝᵘ → ℝᵘ
sqrt x = inf (Σ[ ε ∈ ℚ⁺ ] (x ≤ rational+ (ε ℚ⁺.* ε))) (λ x → rational+ (x .proj₁))

sqrt-correct : ∀ x → (sqrt x * sqrt x) ≃ x
sqrt-correct x .proj₁ .*≤* {ε} x∋ε = λ s → {!!}
sqrt-correct x .proj₂ .*≤* {ε} rx*rx∋ε =
  x .closed λ r →
  let ε₁ , ε₂ , ε₁ε₂≤ε+s , rx∋ε₁ , ry∋ε₂ = rx*rx∋ε r in
  {!!}
  -- inf-greatest {S = λ x → rational+ (x .proj₁)} {!!} .*≤* {ε ℚ⁺.+ r} {!!}
-}

{-
sqrt : ℝᵘ → ℝᵘ
sqrt x .contains q = ∀ δ → x .contains (q qpos.* q qpos.+ δ)
sqrt x .upper q₁≤q₂ = {!!} -- x .upper (qpos.*-mono-≤ q₁≤q₂ q₁≤q₂)
sqrt x .closed {q} h = {!!} -- x .closed (λ s → x .upper {!!} (h (s qpos.* 1/ q)))
-}

{-
sqrt-correct : ∀ x → (sqrt x * sqrt x) ≃ x
sqrt-correct x .proj₁ .*≤* {q} x-q s = {!!} -- need to compute rational square root to within 's' !!!
sqrt-correct x .proj₂ .*≤* sxsx-q = x .closed λ r →
  let q₁ , q₂ , q₁*q₂≤q+s , x-q₁q₁ , x-q₂q₂ = sxsx-q r in
  -- work out which one of q₁ or q₂ is greater
  {!!}
-}
