{-# OPTIONS --without-K --safe #-}

module Data.Real.UpperClosed where

open import Level using (0ℓ; suc)
open import Algebra using (IsMagma;
                           IsSemigroup; IsCommutativeSemigroup;
                           IsMonoid; IsCommutativeMonoid;
                           IsSemiringWithoutAnnihilatingZero;
                           CommutativeSemigroup;
                           Commutative; Congruent₂;
                           LeftIdentity; RightIdentity; Identity;
                           _DistributesOver_;
                           Associative; LeftZero)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Unnormalised as ℚ using () renaming (ℚᵘ to ℚ; 0ℚᵘ to 0ℚ; 1ℚᵘ to 1ℚ)
import Data.Rational.Unnormalised.Properties as ℚ
open import Relation.Nullary using (yes; no; ¬_)
import Data.Rational.Unnormalised.Solver as ℚSolver
open import Relation.Binary using (Antisymmetric; Transitive; Reflexive; IsEquivalence;
                                   IsPreorder; IsPartialOrder; Poset;
                                   _Preserves₂_⟶_⟶_; _⇒_; _Respectsʳ_)

open import Data.Rational.Unnormalised.Positive as ℚ⁺ using (ℚ⁺; _/2; 1/_)

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

-- FIXME: ℚ.+-commutativeSemigroup is missing
open interchange (record
                    { isCommutativeSemigroup = record { isSemigroup = ℚ.+-isSemigroup
                                                      ; comm = ℚ.+-comm } })
   renaming (interchange to ℚ-interchange) public

-- an upper real is a set of upper bounds on a real number; this is
-- the upper half of a MacNellie real number.
record ℝᵘ : Set₁ where
  no-eta-equality -- FIXME: this seems to speed things up
                  -- considerably, and makes goals easier to read
  field
    contains : ℚ⁺ → Set
    upper    : ∀ {q₁ q₂} → q₁ ℚ⁺.≤ q₂ → contains q₁ → contains q₂
    closed   : ∀ {q} → (∀ r → contains (q ℚ⁺.+ r)) → contains q
open ℝᵘ

-- CONJECTURE: the “closed” part can be expressed as begin an
-- algebra for a monad on the category of presheaves over ℚ⁺:
--
--   M x q = ∀ ε. x (q + ε)
--
-- this allows some form of completeness? are we working with a
-- category of sheaves?
--
-- And open ones are coalgebras for a comonad?
--
--   W x q = Σ r. (r < q × x r)
--
-- And MacNellie reals are “two-sided” versions of these, and Dedekind
-- ones add locatedness? Two-sided-ness would mean that we value the
-- presheaves in Chu(Set,⊥) instead of Set.
--
-- Addition and Multiplication are constructed via Day products +
-- completions. But we need different proofs for associativity to be
-- inherited.

infix  4 _≃_
infix  4 _≤_ _<_
-- FIXME: fixity for the arithmetic operations

------------------------------------------------------------------------------
-- Definitions of _≤_ and _≃_

record _≤_ (x y : ℝᵘ) : Set where
  field
    *≤* : ∀ {q} → y .contains q → x .contains q
open _≤_

_≃_ : ℝᵘ → ℝᵘ → Set
x ≃ y = x ≤ y × y ≤ x

------------------------------------------------------------------------------
-- Properties of _≤_ and _≃_

≤-refl : ∀ {x} → x ≤ x
≤-refl .*≤* x-q = x-q

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans x≤y y≤z .*≤* = λ z-q → x≤y .*≤* (y≤z .*≤* z-q)

≃-refl : Reflexive _≃_
≃-refl {x} = ≤-refl {x} , ≤-refl {x}

≃-sym : ∀ {x y} → x ≃ y → y ≃ x
≃-sym (x≤y , y≤x) = y≤x , x≤y

≃-trans : Transitive _≃_
≃-trans (x≤y , y≤x) (y≤z , z≤y) = ≤-trans x≤y y≤z , ≤-trans z≤y y≤x

≤-reflexive : ∀ {x y} → x ≃ y → x ≤ y
≤-reflexive x≃y = x≃y .proj₁

≤-antisym : Antisymmetric _≃_ _≤_
≤-antisym i≤j j≤i = i≤j , j≤i

≃-isEquivalence : IsEquivalence _≃_
≃-isEquivalence = record { refl = ≃-refl ; sym = ≃-sym ; trans = ≃-trans }

≤-isPreOrder : IsPreorder _≃_ _≤_
≤-isPreOrder = record { isEquivalence = ≃-isEquivalence ; reflexive = ≤-reflexive ; trans = ≤-trans }

≤-isPartialOrder : IsPartialOrder _≃_ _≤_
≤-isPartialOrder = record { isPreorder = ≤-isPreOrder ; antisym = ≤-antisym }

≤-poset : Poset (suc 0ℓ) 0ℓ 0ℓ
≤-poset = record { isPartialOrder = ≤-isPartialOrder }

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.PartialOrder ≤-poset public

------------------------------------------------------------------------------
-- Strictly less than, where we are given a positive rational that
-- separates the two numbers.
_<_ : ℝᵘ → ℝᵘ → Set
x < y = Σ[ q ∈ ℚ⁺ ] (x .contains q × ¬ y .contains q)

<-irreflexive : ∀ x → ¬ (x < x)
<-irreflexive x (q , q∈x , ¬q∈x) = ¬q∈x q∈x

<-trans : Transitive _<_
<-trans {x}{y}{z} (q , q∈x , ¬q∈y) (q' , q'∈y , ¬q'∈z) with q ℚ⁺.≤? q'
... | yes q≤q' = q , q∈x , λ q∈z → ¬q'∈z (z .upper q≤q' q∈z)
... | no  b    = ⊥-elim (¬q∈y (y .upper (ℚ⁺.≰⇒≥ b) q'∈y))

<-respʳ-≃ : _<_ Respectsʳ _≃_
<-respʳ-≃ {x}{y₁}{y₂} (y₁≤y₂ , y₂≤y₁) (q , q∈x , ¬q∈y₁) =
  q , q∈x , λ q∈y₂ → ¬q∈y₁ (y₁≤y₂ .*≤* q∈y₂)

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ {x}{y} (q , q∈x , ¬q∈y) .*≤* {q₁} q₁∈y with q ℚ⁺.≤? q₁
... | yes q≤q₁  = x .upper q≤q₁ q∈x
... | no  ¬q≤q₁ = ⊥-elim (¬q∈y (y .upper (ℚ⁺.≰⇒≥ ¬q≤q₁) q₁∈y))

tight-1 : ∀ x y → x ≤ y → ¬ (y < x)
tight-1 x y x≤y (q , q∈y , ¬q∈x) = ¬q∈x (x≤y .*≤* q∈y)

{- -- requires classical logic?
tight-2 : ∀ x y → ¬ (y < x) → x ≤ y
tight-2 x y ¬y<x .*≤* {q} q∈y = ⊥-elim (¬y<x (q , q∈y , {!!}))
-}

------------------------------------------------------------------------------
-- Apartness
_#_ : ℝᵘ → ℝᵘ → Set
x # y = x < y ⊎ y < x

------------------------------------------------------------------------------
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

0-finite : 0ℝ < ∞
0-finite = ℚ⁺.1ℚ⁺ , (tt , (λ z → z))

------------------------------------------------------------------------------
-- Embedding (non negative) rationals

module closedness where
  open import Data.Rational.Unnormalised.Positive
  open import Relation.Binary.PropositionalEquality using (refl)

  2ℚ : ℚ
  2ℚ = ℚ.1ℚᵘ ℚ.+ ℚ.1ℚᵘ

  eq : 2ℚ ℚ.* ℚ.½ ℚ.≃ 1ℚ
  eq = ℚ.*≡* refl

  p<q⇒0<q-p : ∀ {p q} → p ℚ.< q → 0ℚ ℚ.< q ℚ.- p
  p<q⇒0<q-p {p} {q} p<q = begin-strict
    0ℚ       ≈⟨ ℚ.≃-sym (ℚ.+-inverseʳ p) ⟩
    p ℚ.- p  <⟨ ℚ.+-monoˡ-< (ℚ.- p) p<q ⟩
    q ℚ.- p  ∎ where open ℚ.≤-Reasoning

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

  closed' : ∀ a b → (∀ ε → a ℚ.≤ fog (b ℚ⁺.+ ε)) → a ℚ.≤ fog b
  closed' a b h =
    closed₁ a (fog b) λ ε ε>0 → begin
                                 a                         ≤⟨ h (gof ε ε>0) ⟩
                                 fog (b ℚ⁺.+ gof ε ε>0)  ≈⟨ ℚ.*≡* refl ⟩
                                 fog b ℚ.+ ε ∎
      where open ℚ.≤-Reasoning

rational : ℚ → ℝᵘ -- FIXME: should be ℚ≥0
rational r .contains q = r ℚ.≤ ℚ⁺.fog q
rational r .upper q₁≤q₂ r≤q₁ = ℚ.≤-trans r≤q₁ (ℚ⁺.fog-mono q₁≤q₂)
rational r .closed {q} = closedness.closed' r q

{-
-- essentially this holds because closure is a monad, and we are
-- taking the free algebra here.
rational-alt : ℚ → ℝᵘ
rational-alt r .contains q = ∀ ε → r ℚ.≤ ℚ⁺.fog (q ℚ⁺.+ ε)
rational-alt r .upper {q₁}{q₂} q₁≤q₂ r∈q₁ ε =
  begin
    r
  ≤⟨ r∈q₁ ε ⟩
    ℚ⁺.fog (q₁ ℚ⁺.+ ε)
  ≤⟨ ℚ⁺.fog-mono (ℚ⁺.+-mono-≤ q₁≤q₂ (ℚ⁺.≤-refl {ε})) ⟩
    ℚ⁺.fog (q₂ ℚ⁺.+ ε)
  ∎
  where open ℚ.≤-Reasoning
rational-alt r .closed {ε} = {!!}
-}

------------------------------------------------------------------------------
-- Generic construction and proofs for binary operators
module binary-op (_⚈_ : ℚ⁺ → ℚ⁺ → ℚ⁺) (⚈-comm : Commutative ℚ⁺._≃_ _⚈_) where

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

------------------------------------------------------------------------------
-- Addition
open binary-op (ℚ⁺._+_) (ℚ⁺.+-comm)
    renaming ( _⚈ℝ_   to _+_
             ; comm   to +-comm
             ; mono-≤ to +-mono-≤
             ; cong   to +-cong    )
    public

+-identityˡ : LeftIdentity _≃_ 0ℝ _+_
+-identityˡ x .proj₁ .*≤* {q} x-q s =
  s , q , ℚ⁺.≤-reflexive (ℚ⁺.+-comm s q) , tt , x-q
+-identityˡ x .proj₂ .*≤* {q} 0+x =
  x .closed (λ s → let q₁ , q₂ , ineq , tt , x-q₂ = 0+x s in
                    x .upper (ℚ⁺.≤-trans (ℚ⁺.≤-trans ℚ⁺.+-increasing (ℚ⁺.≤-reflexive (ℚ⁺.+-comm q₂ q₁))) ineq) x-q₂)

+-identityʳ : RightIdentity _≃_ 0ℝ _+_
+-identityʳ x = ≃-trans (+-comm x 0ℝ) (+-identityˡ x)

+-identity : Identity _≃_ 0ℝ _+_
+-identity = +-identityˡ , +-identityʳ

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

+-increasingʳ : ∀ x y → x ≤ x + y
+-increasingʳ x y =
  begin
    x           ≈⟨ ≃-sym (+-identityʳ x) ⟩
    x + 0ℝ      ≤⟨ +-mono-≤ ≤-refl (0-least y) ⟩
    x + y       ∎
  where open ≤-Reasoning

+-increasingˡ : ∀ x y → y ≤ x + y
+-increasingˡ x y =
  begin
    y           ≈⟨ ≃-sym (+-identityˡ y) ⟩
    0ℝ + y      ≤⟨ +-mono-≤ (0-least x) ≤-refl ⟩
    x + y       ∎
  where open ≤-Reasoning

+-infinityʳ : ∀ x → (x + ∞) ≃ ∞
+-infinityʳ x .proj₁ = ∞-greatest _
+-infinityʳ x .proj₂ .*≤* {ε} x+∞∋ε =
  let _ , _ , _ , _ , ϕ = x+∞∋ε ℚ⁺.1ℚ⁺ in
  ϕ

------------------------------------------------------------------------------
-- Structures for the algebraic structure of _+_
+-isMagma : IsMagma _≃_ _+_
+-isMagma = record { isEquivalence = ≃-isEquivalence ; ∙-cong = +-cong }

+-isSemigroup : IsSemigroup _≃_ _+_
+-isSemigroup = record { isMagma = +-isMagma ; assoc = +-assoc }

+-isCommutativeSemigroup : IsCommutativeSemigroup _≃_ _+_
+-isCommutativeSemigroup = record { isSemigroup = +-isSemigroup ; comm = +-comm }

+-0-isMonoid : IsMonoid _≃_ _+_ 0ℝ
+-0-isMonoid = record { isSemigroup = +-isSemigroup ; identity = +-identity }

+-0-isCommutativeMonoid : IsCommutativeMonoid _≃_ _+_ 0ℝ
+-0-isCommutativeMonoid = record { isMonoid = +-0-isMonoid ; comm = +-comm }

------------------------------------------------------------------------------
-- Bundles
+-commutativeSemigroup : CommutativeSemigroup (suc 0ℓ) 0ℓ
+-commutativeSemigroup = record { isCommutativeSemigroup = +-isCommutativeSemigroup }

open interchange +-commutativeSemigroup public

------------------------------------------------------------------------------
-- Multiplication
open binary-op (ℚ⁺._*_) (ℚ⁺.*-comm)
    renaming ( _⚈ℝ_   to _*_
             ; comm   to *-comm
             ; mono-≤ to *-mono-≤
             ; cong   to *-cong    )
    public

1ℝ : ℝᵘ
1ℝ = rational 1ℚ

*-zeroʳ : ∀ x → x < ∞ → (x * 0ℝ) ≃ 0ℝ
*-zeroʳ x (ε₁ , x∋ε₁ , _) .proj₁ .*≤* {ε} tt s =
  ε₁ ,
  1/ ε₁ ℚ⁺.* (ε ℚ⁺.+ s) ,
  (begin
    ε₁ ℚ⁺.* (1/ ε₁ ℚ⁺.* (ε ℚ⁺.+ s))
  ≈⟨ ℚ⁺.≃-sym (ℚ⁺.*-assoc ε₁ (1/ ε₁) (ε ℚ⁺.+ s)) ⟩
    (ε₁ ℚ⁺.* 1/ ε₁) ℚ⁺.* (ε ℚ⁺.+ s)
  ≈⟨ ℚ⁺.*-cong (ℚ⁺.*-inverseʳ ε₁) ℚ⁺.≃-refl ⟩
    ℚ⁺.1ℚ⁺ ℚ⁺.* (ε ℚ⁺.+ s)
  ≈⟨ ℚ⁺.*-identityˡ (ε ℚ⁺.+ s) ⟩
    ε ℚ⁺.+ s
  ∎) ,
  x∋ε₁ ,
  tt
  where open ℚ⁺.≤-Reasoning
*-zeroʳ x x<∞ .proj₂ = 0-least (x * 0ℝ)

*-zeroˡ : ∀ x → x < ∞ → (0ℝ * x) ≃ 0ℝ
*-zeroˡ x x<∞ = ≃-trans (*-comm 0ℝ x) (*-zeroʳ x x<∞)

*-infinityʳ : ∀ x → (x * ∞) ≃ ∞
*-infinityʳ x .proj₁ = ∞-greatest _
*-infinityʳ x .proj₂ .*≤* {ε} x∞∋ε =
  let _ , _ , _ , _ , ϕ = x∞∋ε ℚ⁺.1ℚ⁺ in
  ϕ

*-identityˡ : LeftIdentity _≃_ 1ℝ _*_
*-identityˡ x .proj₁ .*≤* {ε} x∋ε s =
  ℚ⁺.1ℚ⁺ ,
  ε ,
  ℚ⁺.≤-trans (ℚ⁺.≤-reflexive (ℚ⁺.*-identityˡ ε)) ℚ⁺.+-increasing ,
  ℚ.≤-refl ,
  x∋ε
*-identityˡ x .proj₂ .*≤* {ε} 1x∋ε =
  x .closed λ s →
  let ε₁ , ε₂ , ε₁ε₂≤ε+s , 1≤ε₁ , x∋ε₂ = 1x∋ε s in
  x .upper
    (begin
      ε₂
    ≈⟨ ℚ⁺.≃-sym (ℚ⁺.*-identityˡ ε₂) ⟩
      ℚ⁺.1ℚ⁺ ℚ⁺.* ε₂
    ≤⟨ ℚ⁺.*-mono-≤ (ℚ⁺.r≤r 1≤ε₁) (ℚ⁺.≤-refl {ε₂}) ⟩
      ε₁ ℚ⁺.* ε₂
    ≤⟨ ε₁ε₂≤ε+s ⟩
      ε ℚ⁺.+ s
    ∎)
    x∋ε₂
    where open ℚ⁺.≤-Reasoning

*-identityʳ : RightIdentity _≃_ 1ℝ _*_
*-identityʳ x = ≃-trans (*-comm x 1ℝ) (*-identityˡ x)

*-identity : Identity _≃_ 1ℝ _*_
*-identity = *-identityˡ , *-identityʳ

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
  ≤⟨ ℚ⁺.*-mono-≤ (ℚ⁺.≤-refl {ε₁}) ε₂₁ε₂₂≤ε₂+s ⟩
    ε₁ ℚ⁺.* (ε₂ ℚ⁺.+ (1/ ε₁ ℚ⁺.* s /2))
  ≈⟨ ℚ⁺.*-distribˡ-+ ε₁ ε₂ (1/ ε₁ ℚ⁺.* s /2) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ ε₁ ℚ⁺.* (1/ ε₁ ℚ⁺.* s /2)
  ≈⟨ ℚ⁺.+-congʳ (ε₁ ℚ⁺.* ε₂) (ℚ⁺.≃-sym (ℚ⁺.*-assoc ε₁ (1/ ε₁) (s /2))) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ (ε₁ ℚ⁺.* 1/ ε₁) ℚ⁺.* s /2
  ≈⟨ ℚ⁺.+-congʳ (ε₁ ℚ⁺.* ε₂) (ℚ⁺.*-congˡ (s /2) (ℚ⁺.*-inverseʳ ε₁)) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ ℚ⁺.1ℚ⁺ ℚ⁺.* s /2
  ≈⟨ ℚ⁺.+-congʳ (ε₁ ℚ⁺.* ε₂) (ℚ⁺.*-identityˡ (s /2)) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ s /2
  ≤⟨ ℚ⁺.+-mono-≤ ε₁ε₂≤ε+s (ℚ⁺.≤-refl {s /2}) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
  ≈⟨ ℚ⁺.+-assoc ε (s /2) (s /2) ⟩
    ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
  ≈⟨ ℚ⁺.+-congʳ ε ℚ⁺.half+half ⟩
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
  ≈⟨ ℚ⁺.≃-sym (ℚ⁺.*-assoc ε₁₁ ε₁₂ ε₂) ⟩
    (ε₁₁ ℚ⁺.* ε₁₂) ℚ⁺.* ε₂
  ≤⟨ ℚ⁺.*-mono-≤ ε₁₁ε₁₂≤ε₁+ (ℚ⁺.≤-refl {ε₂}) ⟩
    (ε₁ ℚ⁺.+ (s /2 ℚ⁺.* 1/ ε₂)) ℚ⁺.* ε₂
  ≈⟨ ℚ⁺.*-distribʳ-+ ε₂ ε₁ (s /2 ℚ⁺.* 1/ ε₂) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ (s /2 ℚ⁺.* 1/ ε₂) ℚ⁺.* ε₂
  ≈⟨ ℚ⁺.+-congʳ (ε₁ ℚ⁺.* ε₂) (ℚ⁺.*-assoc (s /2) (1/ ε₂) ε₂) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ s /2 ℚ⁺.* (1/ ε₂ ℚ⁺.* ε₂)
  ≈⟨ ℚ⁺.+-congʳ (ε₁ ℚ⁺.* ε₂) (ℚ⁺.*-congʳ (s /2) (ℚ⁺.*-inverseˡ ε₂)) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ s /2 ℚ⁺.* ℚ⁺.1ℚ⁺
  ≈⟨ ℚ⁺.+-congʳ (ε₁ ℚ⁺.* ε₂) (ℚ⁺.*-identityʳ (s /2)) ⟩
    ε₁ ℚ⁺.* ε₂ ℚ⁺.+ s /2
  ≤⟨ ℚ⁺.+-mono-≤ ε₁ε₂≤ε+ (ℚ⁺.≤-refl {s /2}) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
  ≈⟨ ℚ⁺.+-assoc ε (s /2) (s /2) ⟩
    ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
  ≈⟨ ℚ⁺.+-congʳ ε ℚ⁺.half+half ⟩
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
  ≤⟨ ℚ⁺.+-mono-≤ (ℚ⁺.*-mono-≤ (ℚ⁺.≤-refl {ε₁₁}) (ℚ⁺.⊓-lower-1 ε₁₂ ε₂₂)) (ℚ⁺.*-mono-≤ (ℚ⁺.≤-refl {ε₂₁}) (ℚ⁺.⊓-lower-2 ε₁₂ ε₂₂)) ⟩
    ε₁₁ ℚ⁺.* ε₁₂ ℚ⁺.+ ε₂₁ ℚ⁺.* ε₂₂
  ≤⟨ ℚ⁺.+-mono-≤ ε₁₁ε₁₂≤ε₁+ ε₂₁ε₂₂≤ε₂+ ⟩
    (ε₁ ℚ⁺.+ s /2 /2) ℚ⁺.+ (ε₂ ℚ⁺.+ s /2 /2)
  ≈⟨ ℚ⁺-interchange ε₁ (s /2 /2) ε₂ (s /2 /2) ⟩
    (ε₁ ℚ⁺.+ ε₂) ℚ⁺.+ (s /2 /2 ℚ⁺.+ s /2 /2)
  ≈⟨ ℚ⁺.+-congʳ (ε₁ ℚ⁺.+ ε₂) (ℚ⁺.half+half {s /2}) ⟩
    (ε₁ ℚ⁺.+ ε₂) ℚ⁺.+ s /2
  ≤⟨ ℚ⁺.+-mono-≤ ε₁+ε₂≤ε+ (ℚ⁺.≤-refl {s /2}) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
  ≈⟨ ℚ⁺.+-assoc ε (s /2) (s /2) ⟩
    ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
  ≈⟨ ℚ⁺.+-congʳ ε (ℚ⁺.half+half {s}) ⟩
    ε ℚ⁺.+ s
  ∎) ,
  (λ r → ε₁₁ , ε₂₁ , ℚ⁺.+-increasing , y∋ε₁₁ , z∋ε₂₁) ,
  x∋⊓ ε₁₂ ε₂₂ x∋ε₁₂ x∋ε₂₂
  where open ℚ⁺.≤-Reasoning
        x∋⊓ : ∀ ε₁ ε₂ → x .contains ε₁ → x .contains ε₂ → x .contains (ε₁ ℚ⁺.⊓ ε₂)
        x∋⊓ ε₁ ε₂ x∋ε₁ x∋ε₂ with ℚ⁺.⊓-selective ε₁ ε₂
        x∋⊓ ε₁ ε₂ x∋ε₁ x∋ε₂ | inj₁ p = x .upper (ℚ⁺.≤-reflexive (ℚ⁺.≃-sym p)) x∋ε₁
        x∋⊓ ε₁ ε₂ x∋ε₁ x∋ε₂ | inj₂ p = x .upper (ℚ⁺.≤-reflexive (ℚ⁺.≃-sym p)) x∋ε₂
*-distribʳ-+ x y z .proj₂ .*≤* {ε} [y+z]x∋ε s =
  let ε₁ , ε₂ , ε₁ε₂≤ε+ , y+z∋ε₁ , x∋ε₂ = [y+z]x∋ε (s /2) in
  let ε₁₁ , ε₁₂ , ε₁₁+ε₁₂≤ε₁+ , y∋ε₁₁ , z∋ε₁₂ = y+z∋ε₁ (s /2 ℚ⁺.* 1/ ε₂) in
  ε₁₁ ℚ⁺.* ε₂ ,
  ε₁₂ ℚ⁺.* ε₂ ,
  (begin
    (ε₁₁ ℚ⁺.* ε₂) ℚ⁺.+ (ε₁₂ ℚ⁺.* ε₂)
  ≈⟨ ℚ⁺.≃-sym (ℚ⁺.*-distribʳ-+ ε₂ ε₁₁ ε₁₂) ⟩
    (ε₁₁ ℚ⁺.+ ε₁₂) ℚ⁺.* ε₂
  ≤⟨ ℚ⁺.*-mono-≤ ε₁₁+ε₁₂≤ε₁+ (ℚ⁺.≤-refl {ε₂}) ⟩
    (ε₁ ℚ⁺.+ (s /2 ℚ⁺.* 1/ ε₂)) ℚ⁺.* ε₂
  ≈⟨ ℚ⁺.*-distribʳ-+ ε₂ ε₁ (s /2 ℚ⁺.* 1/ ε₂) ⟩
    (ε₁ ℚ⁺.* ε₂) ℚ⁺.+ (s /2 ℚ⁺.* 1/ ε₂) ℚ⁺.* ε₂
  ≈⟨ ℚ⁺.+-congʳ (ε₁ ℚ⁺.* ε₂) (ℚ⁺.*-assoc (s /2) (1/ ε₂) ε₂) ⟩
    (ε₁ ℚ⁺.* ε₂) ℚ⁺.+ s /2 ℚ⁺.* (1/ ε₂ ℚ⁺.* ε₂)
  ≈⟨ ℚ⁺.+-congʳ (ε₁ ℚ⁺.* ε₂) (ℚ⁺.*-congʳ (s /2) (ℚ⁺.*-inverseˡ ε₂)) ⟩
    (ε₁ ℚ⁺.* ε₂) ℚ⁺.+ s /2 ℚ⁺.* ℚ⁺.1ℚ⁺
  ≈⟨ ℚ⁺.+-congʳ (ε₁ ℚ⁺.* ε₂) (ℚ⁺.*-identityʳ (s /2)) ⟩
    (ε₁ ℚ⁺.* ε₂) ℚ⁺.+ s /2
  ≤⟨ ℚ⁺.+-mono-≤ ε₁ε₂≤ε+ (ℚ⁺.≤-refl {s /2}) ⟩
    (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
  ≈⟨ ℚ⁺.+-assoc ε (s /2) (s /2) ⟩
    ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
  ≈⟨ ℚ⁺.+-congʳ ε (ℚ⁺.half+half {s}) ⟩
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

*-distrib-+ : _DistributesOver_ _≃_ _*_ _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

------------------------------------------------------------------------------
-- Structures for the algebraic structure of _*_

*-isMagma : IsMagma _≃_ _*_
*-isMagma = record { isEquivalence = ≃-isEquivalence ; ∙-cong = *-cong }

*-isSemigroup : IsSemigroup _≃_ _*_
*-isSemigroup = record { isMagma = *-isMagma ; assoc = *-assoc }

*-isCommutativeSemigroup : IsCommutativeSemigroup _≃_ _*_
*-isCommutativeSemigroup = record { isSemigroup = *-isSemigroup ; comm = *-comm }

*-1-isMonoid : IsMonoid _≃_ _*_ 1ℝ
*-1-isMonoid = record { isSemigroup = *-isSemigroup ; identity = *-identity }

*-1-isCommutativeMonoid : IsCommutativeMonoid _≃_ _*_ 1ℝ
*-1-isCommutativeMonoid = record { isMonoid = *-1-isMonoid ; comm = *-comm }

isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _≃_ _+_ _*_ 0ℝ 1ℝ
isSemiringWithoutAnnihilatingZero =
  record { +-isCommutativeMonoid = +-0-isCommutativeMonoid
         ; *-isMonoid            = *-1-isMonoid
         ; distrib               = *-distrib-+ }

------------------------------------------------------------------------------
-- FIXME: Bundles

------------------------------------------------------------------------------
-- Properties of embedding rationals

rational-mono : ∀ {q r} → q ℚ.≤ r → rational q ≤ rational r
rational-mono q≤r .*≤* = ℚ.≤-trans q≤r

rational-cong : ∀ {q r} → q ℚ.≃ r → rational q ≃ rational r
rational-cong q≃r .proj₁ = rational-mono (ℚ.≤-reflexive q≃r)
rational-cong q≃r .proj₂ = rational-mono (ℚ.≤-reflexive (ℚ.≃-sym q≃r))

rational+ : ℚ⁺ → ℝᵘ
rational+ q = rational (ℚ⁺.fog q)

rational-mono-reflect : ∀ {q r} → rational q ≤ rational+ r → q ℚ.≤ ℚ⁺.fog r
rational-mono-reflect {q}{r} q≤r = q≤r .*≤* {r} ℚ.≤-refl

rational-0 : rational 0ℚ ≃ 0ℝ
rational-0 .proj₁ .*≤* {q} tt = ℚ⁺.fog-nonneg q
rational-0 .proj₂ = 0-least _

rational-+ : ∀ q r → 0ℚ ℚ.≤ q → 0ℚ ℚ.≤ r → (rational q + rational r) ≃ rational (q ℚ.+ r)
rational-+ q r 0≤q 0≤r .proj₁ .*≤* {ε} q+r≤ε s =
  ℚ⁺.nn+pos q (s /2) 0≤q ,
  ℚ⁺.nn+pos r (s /2) 0≤r ,
  ℚ⁺.r≤r (begin
              q ℚ.+ ℚ⁺.fog (s /2) ℚ.+ (r ℚ.+ ℚ⁺.fog (s /2))
            ≈⟨ ℚ-interchange q (ℚ⁺.fog (s /2)) r (ℚ⁺.fog (s /2)) ⟩
              (q ℚ.+ r) ℚ.+ (ℚ⁺.fog (s /2) ℚ.+ ℚ⁺.fog (s /2))
            ≈⟨ ℚ.+-congʳ (q ℚ.+ r) (ℚ.≃-sym (ℚ⁺.+-fog (s /2) (s /2))) ⟩
              (q ℚ.+ r) ℚ.+ ℚ⁺.fog (s /2 ℚ⁺.+ s /2)
            ≤⟨ ℚ.+-mono-≤ q+r≤ε (ℚ⁺.fog-mono (ℚ⁺.≤-reflexive (ℚ⁺.half+half {s}))) ⟩
              ℚ⁺.fog ε ℚ.+ ℚ⁺.fog s
            ≈⟨ ℚ⁺.+-fog ε s ⟩
              ℚ⁺.fog (ε ℚ⁺.+ s)
           ∎) ,
  ℚ⁺.q≤nn+pos q (s /2) ,
  ℚ⁺.q≤nn+pos r (s /2)
  where open ℚ.≤-Reasoning
rational-+ q r 0≤q 0≤r .proj₂ .*≤* {ε} q+r∋ε =
  rational (q ℚ.+ r) .closed {ε} λ s →
  let ε₁ , ε₂ , ε₁+ε₂≤ε+s , q≤ε₁ , r≤ε₂ = q+r∋ε s in
  begin
    q ℚ.+ r
  ≤⟨ ℚ.+-mono-≤ q≤ε₁ r≤ε₂ ⟩
    ℚ⁺.fog ε₁ ℚ.+ ℚ⁺.fog ε₂
  ≈⟨ ℚ.≃-sym (ℚ⁺.+-fog ε₁ ε₂) ⟩
    ℚ⁺.fog (ε₁ ℚ⁺.+ ε₂)
  ≤⟨ ℚ⁺.fog-mono ε₁+ε₂≤ε+s ⟩
    ℚ⁺.fog (ε ℚ⁺.+ s)
  ∎
  where open ℚ.≤-Reasoning

rational⁺-* : ∀ q r → (rational+ q * rational+ r) ≃ rational+ (q ℚ⁺.* r)
rational⁺-* q r .proj₁ .*≤* {ε} qr≤ε s =
  q ,
  r ,
  (begin
    q ℚ⁺.* r
  ≤⟨ ℚ⁺.r≤r qr≤ε ⟩
    ε
  ≤⟨ ℚ⁺.+-increasing ⟩
    ε ℚ⁺.+ s
  ∎) ,
  ℚ.≤-refl ,
  ℚ.≤-refl
  where open ℚ⁺.≤-Reasoning
rational⁺-* q r .proj₂ .*≤* {ε} qr∋ε =
  rational+ (q ℚ⁺.* r) .closed {ε} λ s →
  let ε₁ , ε₂ , ε₁ε₂≤ε+s , q≤ε₁ , r≤ε₂ = qr∋ε s in
  begin
    ℚ⁺.fog q ℚ.* ℚ⁺.fog r
  ≤⟨ ℚ.*-monoʳ-≤-pos {ℚ⁺.fog q} (ℚ.positive (ℚ⁺.fog-positive q)) r≤ε₂ ⟩
    ℚ⁺.fog q ℚ.* ℚ⁺.fog ε₂
  ≤⟨ ℚ.*-monoˡ-≤-pos (ℚ.positive (ℚ⁺.fog-positive ε₂)) q≤ε₁ ⟩
    ℚ⁺.fog ε₁ ℚ.* ℚ⁺.fog ε₂
  ≈⟨ ℚ.≃-sym (ℚ⁺.*-fog ε₁ ε₂) ⟩
    ℚ⁺.fog (ε₁ ℚ⁺.* ε₂)
  ≤⟨ ℚ⁺.fog-mono ε₁ε₂≤ε+s ⟩
    ℚ⁺.fog (ε ℚ⁺.+ s)
  ∎
  where open ℚ.≤-Reasoning

rational⁺-+ : ∀ q r → (rational+ q + rational+ r) ≃ rational+ (q ℚ⁺.+ r)
rational⁺-+ q r =
  begin-equality
    rational+ q + rational+ r
  ≡⟨⟩
    rational (ℚ⁺.fog q) + rational (ℚ⁺.fog r)
  ≈⟨ rational-+ (ℚ⁺.fog q) (ℚ⁺.fog r) (ℚ⁺.fog-nonneg q) (ℚ⁺.fog-nonneg r) ⟩
    rational (ℚ⁺.fog q ℚ.+ ℚ⁺.fog r)
  ≈⟨ rational-cong (ℚ⁺.+-fog q r) ⟩
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
... | Relation.Binary.tri< a ¬b ¬c = rational+<∞ ℚ⁺.⟨ q , (ℚ.positive a) ⟩
... | Relation.Binary.tri≈ ¬a b ¬c = ℚ⁺.1ℚ⁺ , ℚ.≤-trans (ℚ.≤-reflexive (ℚ.≃-sym b)) 0≤1 , λ x → x
... | Relation.Binary.tri> ¬a ¬b c = ℚ⁺.1ℚ⁺ , ℚ.<⇒≤ (ℚ.<-≤-trans c 0≤1) , λ x → x

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
  ≈⟨ rational⁺-* ℚ⁺.⟨ q , ℚ.positive 0<q ⟩ ℚ⁺.⟨ r , ℚ.positive 0<r ⟩ ⟩
    rational (q ℚ.* r)
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
-- truncating subtraction, which is essentially an exponential
-- ("residual") in the reversed poset.
_⊝_ : ℝᵘ → ℝᵘ → ℝᵘ
(x ⊝ y) .contains ε =
  ∀ ε' → y .contains ε' → x .contains (ε ℚ⁺.+ ε')
(x ⊝ y) .upper ε₁≤ε₂ h ε' y∋ε' =
  x .upper (ℚ⁺.+-mono-≤ ε₁≤ε₂ ℚ⁺.≤-refl) (h ε' y∋ε')
(x ⊝ y) .closed {ε} h ε' y∋ε' =
  x .closed λ s → x .upper (ℚ⁺.≤-reflexive (eq s)) (h s ε' y∋ε')
  where open import Algebra.Solver.CommutativeSemigroup (ℚ⁺.+-commutativeSemigroup)
        a = v# 0; b = v# 1; c = v# 2
        eq : ∀ s → ε ℚ⁺.+ s ℚ⁺.+ ε' ℚ⁺.≃ ε ℚ⁺.+ ε' ℚ⁺.+ s
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
  ℚ⁺.≤-trans (ℚ⁺.≤-reflexive (ℚ⁺.+-comm ε' ε)) ℚ⁺.+-increasing ,
  y∋ε' ,
  z∋ε

------------------------------------------------------------------------------
-- FIXME: this is the old truncating subtraction, just for rationals
_⊖_ : ℝᵘ → ℚ⁺ → ℝᵘ
(x ⊖ r) .contains q = x .contains (q ℚ⁺.+ r)
(x ⊖ r) .upper q₁≤q₂ = x .upper (ℚ⁺.+-mono-≤ q₁≤q₂ ℚ⁺.≤-refl)
(x ⊖ r) .closed {q} h =
  x .closed (λ s → x .upper (ℚ⁺.≤-reflexive (prove 3 ((a ⊕ b) ⊕ c) ((a ⊕ c) ⊕ b) (q ∷ s ∷ r ∷ []))) (h s))
  where open import Algebra.Solver.CommutativeSemigroup (ℚ⁺.+-commutativeSemigroup)
        a = v# 0; b = v# 1; c = v# 2

⊖-iso1 : ∀ {x q y} → (x ⊖ q) ≤ y → x ≤ (y + rational+ q)
⊖-iso1 {x}{q}{y} x⊖q≤y .*≤* {ε} h =
  x .closed λ s →
  let ε₁ , ε₂ , ε₁+ε₂≤ε+s , y-ε₁ , q≤ε₂ = h s in
  x .upper ε₁+ε₂≤ε+s (x .upper (ℚ⁺.+-mono-≤ ℚ⁺.≤-refl (ℚ⁺.r≤r q≤ε₂)) (x⊖q≤y .*≤* y-ε₁))

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
   ℚ⁺.fog-mono {r} {q ℚ⁺.+ r} (ℚ⁺.≤-trans ℚ⁺.+-increasing (ℚ⁺.≤-reflexive (ℚ⁺.+-comm r q)))

⊖-≤ : ∀ {x ε} → (x ⊖ ε) ≤ x
⊖-≤ {x} .*≤* = x .upper ℚ⁺.+-increasing

-- FIXME: this is the same proof twice
-- FIXME: in the light of the above observation that ⊖ is a Day exponential, this is currying
⊖-+ : ∀ {x q r} → ((x ⊖ q) ⊖ r) ≃ (x ⊖ (q ℚ⁺.+ r))
⊖-+ {x}{q}{r} .proj₁ .*≤* {ε} =
   x .upper (ℚ⁺.≤-reflexive (ℚ⁺.≃-trans (ℚ⁺.+-congʳ ε (ℚ⁺.+-comm q r)) (ℚ⁺.≃-sym (ℚ⁺.+-assoc ε r q))))
⊖-+ {x}{q}{r} .proj₂ .*≤* {ε} =
   x .upper (ℚ⁺.≤-reflexive (ℚ⁺.≃-trans (ℚ⁺.+-assoc ε r q) (ℚ⁺.+-congʳ ε (ℚ⁺.+-comm r q))))

-- FIXME: deduce this from the exponential isomorphisms
⊖-+-+ : ∀ {x y q r} → ((x + y) ⊖ (q ℚ⁺.+ r)) ≤ ((x ⊖ q) + (y ⊖ r))
⊖-+-+ {x}{y}{q}{r} .*≤* {ε} h s =
  let ε₁ , ε₂ , ε₁+ε₂≤ε+s , x-ε₁ , y-ε₂ = h s in
  ε₁ ℚ⁺.+ q , ε₂ ℚ⁺.+ r ,
  (begin
    (ε₁ ℚ⁺.+ q) ℚ⁺.+ (ε₂ ℚ⁺.+ r)
      ≈⟨ ℚ⁺-interchange ε₁ q ε₂ r ⟩
    (ε₁ ℚ⁺.+ ε₂) ℚ⁺.+ (q ℚ⁺.+ r)
      ≤⟨ ℚ⁺.+-mono-≤ ε₁+ε₂≤ε+s ℚ⁺.≤-refl ⟩
    (ε ℚ⁺.+ s) ℚ⁺.+ (q ℚ⁺.+ r)
      ≈⟨ ℚ⁺.+-assoc ε s (q ℚ⁺.+ r) ⟩
    ε ℚ⁺.+ (s ℚ⁺.+ (q ℚ⁺.+ r))
      ≈⟨ ℚ⁺.+-congʳ ε (ℚ⁺.+-comm s (q ℚ⁺.+ r)) ⟩
    ε ℚ⁺.+ ((q ℚ⁺.+ r) ℚ⁺.+ s)
      ≈⟨ ℚ⁺.≃-sym (ℚ⁺.+-assoc ε (q ℚ⁺.+ r) s) ⟩
    ε ℚ⁺.+ (q ℚ⁺.+ r) ℚ⁺.+ s
  ∎) ,
  x-ε₁ , y-ε₂
  where open ℚ⁺.≤-Reasoning

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
-- binary maximum
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
-- binary minimum
_⊓_ : ℝᵘ → ℝᵘ → ℝᵘ
(x ⊓ y) .contains q = ∀ s → x .contains (q ℚ⁺.+ s) ⊎ y .contains (q ℚ⁺.+ s)
(x ⊓ y) .upper q₁≤q₂ v s =
  [ (λ x-q₁+s → inj₁ (x .upper (ℚ⁺.+-mono-≤ q₁≤q₂ ℚ⁺.≤-refl) x-q₁+s)) , (λ y-q₁+s → inj₂ (y .upper (ℚ⁺.+-mono-≤ q₁≤q₂ ℚ⁺.≤-refl) y-q₁+s)) ] (v s)
(x ⊓ y) .closed h s with h (s /2) (s /2)
... | inj₁ p = inj₁ (x .upper (ℚ⁺.≤-reflexive (ℚ⁺.≃-trans (ℚ⁺.+-assoc _ _ _) (ℚ⁺.+-congʳ _ (ℚ⁺.half+half {s})))) p)
... | inj₂ p = inj₂ (y .upper (ℚ⁺.≤-reflexive (ℚ⁺.≃-trans (ℚ⁺.+-assoc _ _ _) (ℚ⁺.+-congʳ _ (ℚ⁺.half+half {s})))) p)

⊓-lower-1 : ∀ {x y} → (x ⊓ y) ≤ x
⊓-lower-1 {x}{y} .*≤* x-q s = inj₁ (x .upper ℚ⁺.+-increasing x-q)

⊓-lower-2 : ∀ {x y} → (x ⊓ y) ≤ y
⊓-lower-2 {x}{y} .*≤* y-q s = inj₂ (y .upper ℚ⁺.+-increasing y-q)

⊓-greatest : ∀ {x y z} → x ≤ y → x ≤ z → x ≤ (y ⊓ z)
⊓-greatest {x} x≤y x≤z .*≤* y⊓z-q = x .closed λ s → [ x≤y .*≤* , x≤z .*≤* ] (y⊓z-q s)

-- FIXME: I guess min and max distribute?

-- FIXME: rational (at least for non-negative numbers) preserves min and max?
-- preservation of minimum will require the closedness? because it is the preservation of colimits via the Yoneda embedding?


-- FIXME: min and max preserve _+_ and _*_ ??

------------------------------------------------------------------------------
-- general suprema / least upper bounds / (pointwise) limits
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

-- FIXME: is this an equality?
sup-+ : ∀ {I J} {S₁ : I → ℝᵘ} {S₂ : J → ℝᵘ} →
        sup (I × J) (λ ij → S₁ (proj₁ ij) + S₂ (proj₂ ij)) ≤ (sup I S₁ + sup J S₂)
sup-+ = sup-least λ i → +-mono-≤ (sup-upper _) (sup-upper _)

-- There are no elements infinitesimally below 'y'
approximate : ∀ y → y ≤ sup ℚ⁺ (λ ε → y ⊖ ε)
approximate y .*≤* h = y .closed h
-- FIXME: “closedness” above is now a consequence of this

{- -- this isn't true... cannot approximate numbers from below in this
   -- system; numbers are only “half complete”.

sup-approx : ∀ y → y ≃ sup (Σ[ q ∈ ℚ⁺ ] (rational+ q ≤ y)) (λ i → rational+ (i .proj₁))
sup-approx y .proj₁ .*≤* {ε} h = {!!}
sup-approx y .proj₂ = sup-least (λ i → i .proj₂)
-}

sup-0 : sup ⊥ (λ ()) ≃ 0ℝ
sup-0 .proj₁ .*≤* tt ()
sup-0 .proj₂ = 0-least _

------------------------------------------------------------------------------
-- infima / greatest lower bounds / colimits

inf : (I : Set) → (I → ℝᵘ) → ℝᵘ
inf I S .contains q = ∀ s → Σ[ i ∈ I ] (S i .contains (q ℚ⁺.+ s))
inf I S .upper q≤r contains-q s =
  let i , p = contains-q s in
  i , S i .upper (ℚ⁺.+-mono-≤ q≤r ℚ⁺.≤-refl) p
inf I S .closed {ε} h s =
  let i , p = h (s /2) (s /2) in
  i , S i .upper (ℚ⁺.≤-reflexive (ℚ⁺.≃-trans (ℚ⁺.+-assoc ε (s /2) (s /2)) (ℚ⁺.+-congʳ ε ℚ⁺.half+half))) p

inf-lower : ∀ {I S} i → inf I S ≤ S i
inf-lower {I}{S} i .*≤* {ε} Si∋ε s = i , S i .upper ℚ⁺.+-increasing Si∋ε

inf-greatest : ∀ {I S x} → (∀ i → x ≤ S i) → x ≤ inf I S
inf-greatest {I}{S}{x} h .*≤* {ε} infIS∋ε =
  x .closed λ s →
  let i , Si∋ε+s = infIS∋ε s in
  h i .*≤* Si∋ε+s

-- Another statement of the archimedian principle? But this doesn't
-- use .closed? Maybe that's because it is specialised to 0?
inf-ℚ⁺ : inf ℚ⁺ rational+ ≃ 0ℝ
inf-ℚ⁺ .proj₁ .*≤* {ε} tt s = ε , ℚ⁺.fog-mono (ℚ⁺.+-increasing {ε} {s})
inf-ℚ⁺ .proj₂ = 0-least _

inf-empty : inf ⊥ (λ ()) ≃ ∞
inf-empty .proj₁ = ∞-greatest _
inf-empty .proj₂ = inf-greatest (λ ())

-- FIXME: surely this is possible without unpacking the definition of ℝᵘ?
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
        ≤⟨ ℚ⁺.+-mono-≤ ε₁+ε₂≤ε+ (ℚ⁺.≤-refl {s /2}) ⟩
          (ε ℚ⁺.+ s /2) ℚ⁺.+ s /2
        ≈⟨ ℚ⁺.+-assoc ε (s /2) (s /2) ⟩
          ε ℚ⁺.+ (s /2 ℚ⁺.+ s /2)
        ≈⟨ ℚ⁺.+-congʳ ε (ℚ⁺.half+half {s}) ⟩
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
-- or: every presheaf is a colimit of representables???
approx : ∀ y → y ≃ inf (Σ[ q ∈ ℚ⁺ ] (y ≤ rational+ q)) (λ i → rational+ (i .proj₁))
approx y .proj₁ = inf-greatest (λ i → i .proj₂)
approx y .proj₂ .*≤* {ε} y∋ε s =
  (ε , (record { *≤* = λ x → y .upper (ℚ⁺.r≤r x) y∋ε })) , ℚ⁺.fog-mono (ℚ⁺.+-increasing {ε}{s})


------------------------------------------------------------------------------
-- Axiomatic definition of truncating subtraction in terms of infima,
-- based on the equation in as-inf. If this works, then we'd be able
-- to abstract the definition of metric space over the type of reals,
-- and just assume that it is  when defining the completion.

as-inf : ∀ x y → (x ⊝ y) ≃ inf (Σ[ q ∈ ℚ⁺ ] (x ≤ (y + rational+ q))) (λ x → rational+ (x .proj₁))
as-inf x y .proj₁ = inf-greatest (λ i → residual-2 (i .proj₂))
as-inf x y .proj₂ =
  ≤-trans
    (inf-greatest (λ i → inf-lower (i .proj₁ , residual-1 (i .proj₂))))
    (≤-reflexive (≃-sym (approx (x ⊝ y))))

_∸_ : ℝᵘ → ℝᵘ → ℝᵘ
(x ∸ y) = inf (Σ[ q ∈ ℚ⁺ ] (x ≤ y + rational+ q)) λ qp → rational+ (qp .proj₁)

-- x ∸ y = ⋀{z | x ≤ y + z}   (approximated as rationals)

{-
residual-1' : ∀ {x y z} → (x ∸ y) ≤ z → x ≤ (y + z)
residual-1' {x}{y}{z} x∸y≤z =
  begin
    x
  ≈⟨ approx x ⟩
    inf (Σ[ q ∈ ℚ⁺ ] (x ≤ rational+ q)) (λ i → rational+ (i .proj₁))
  ≤⟨ {!!} ⟩
    y + z
  ∎
  where open ≤-Reasoning
-}

residual-2' : ∀ {x y z} → x ≤ (y + z) → (x ∸ y) ≤ z
residual-2' {x}{y}{z} x≤y+z =
  begin
    x ∸ y
  ≡⟨⟩
    inf (Σ[ q ∈ ℚ⁺ ] (x ≤ y + rational+ q)) (λ qp → rational+ (qp .proj₁))
  ≤⟨ inf-greatest (λ i → inf-lower (i .proj₁ , lemma (i .proj₂))) ⟩
    inf (Σ[ q ∈ ℚ⁺ ] (z ≤ rational+ q)) (λ i → rational+ (i .proj₁))
  ≈⟨ ≃-sym (approx z) ⟩
    z
  ∎
  where open ≤-Reasoning
        lemma : ∀ {w} → z ≤ w → x ≤ y + w
        lemma {w} z≤w =
          begin
            x          ≤⟨ x≤y+z ⟩
            y + z      ≤⟨ +-mono-≤  ≤-refl z≤w ⟩
            y + w      ∎

------------------------------------------------------------------------------
sqrt : ℝᵘ → ℝᵘ
sqrt x = inf (Σ[ q ∈ ℚ⁺ ] (x ≤ rational+ (q ℚ⁺.* q))) (λ x → rational+ (x .proj₁))

{-
inf-* : ∀ {I₁ I₂ S₁ S₂} →
        inf (I₁ × I₂) (λ i → S₁ (i .proj₁) * S₂ (i .proj₂)) ≃ (inf I₁ S₁ * inf I₂ S₂)
inf-* {I₁}{I₂}{S₁}{S₂} .proj₁ = {!!}
inf-* {I₁}{I₂}{S₁}{S₂} .proj₂ =
  {!begin
    inf I₁ S₁ * inf I₂ S₂
  ≤⟨ ? ⟩
    inf (I₁ × I₂) (λ i → S₁ (i .proj₁) * S₂ (i .proj₂))
  ∎!}
  where open ≤-Reasoning
-}

{-
sqrt-correct : ∀ x → (sqrt x * sqrt x) ≃ x
sqrt-correct x .proj₁ =
  begin
    sqrt x * sqrt x
  ≤⟨ inf-greatest {!!} ⟩
    inf (Σ[ q ∈ ℚ⁺ ] (x ≤ rational+ q)) (λ i → rational+ (i .proj₁))
  ≈⟨ ≃-sym (approx x) ⟩
    x
  ∎
  where open ≤-Reasoning
sqrt-correct x .proj₂ = {!!}
-}

{-
sqrt-correct : ∀ x → (sqrt x * sqrt x) ≃ x
sqrt-correct x .proj₁ .*≤* {q} q∈x ε =
  let √q : ℚ⁺
      √q = {!!} in -- with the property that √q * √q ≤ q + ε
  √q , √q , {!!} , (λ s → (√q {- +ε ? -}, (record { *≤* = λ x₁ → x .upper {!!} q∈x })) , {!!}) , {!!} -- compute the square root of 'q' to within ε over.
sqrt-correct x .proj₂ .*≤* {q} √x*√x∋q =
  x .closed λ ε →
  let q₁ , q₂ , q₁q₂≤q+ε , √x∋q₁ , √y∋q₂ = √x*√x∋q ε in
  {!√x∋q₁ (ε /2)!} -- FIXME : todo; might need to work out which of q₁ or q₂ is greater
-}
