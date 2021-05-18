{-# OPTIONS --without-K --safe #-}

open import Algebra

module CommutativeSemigroupSolver {m₁ m₂} (G : CommutativeSemigroup m₁ m₂) where

open import Data.Maybe as Maybe
import Relation.Binary.PropositionalEquality as PropositionalEquality

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; #_)
open import Data.Vec as Vec using (Vec)
open import Data.Vec using (_∷_; []) public
open import Data.Vec.Properties using (lookup-map)
open import Relation.Nullary.Decidable.Core using (True)

import MonoidOfSemigroup (G) as M
import Algebra.Solver.CommutativeMonoid
module Solver = Algebra.Solver.CommutativeMonoid (M.⊕-u-commutativeMonoid)

open CommutativeSemigroup G using () renaming (_≈_ to _≈'_; Carrier to InnerCarrier; _∙_ to _∙'_)
open CommutativeMonoid M.⊕-u-commutativeMonoid using (Carrier; _≈_; reflexive; setoid; _∙_; ∙-cong; refl; sym)
open M using (`_; embedding) public
open Solver using (Expr; ⟦_⟧; normalise; module R; ⟦_⟧⇓; _≟_)

lift-env : ∀ {n} → Vec InnerCarrier n → Vec Carrier n
lift-env = Vec.map (`_)

data Expr' : ℕ → Set where
  var : ∀ {n} → Fin n → Expr' n
  _⊕_ : ∀ {n} → Expr' n → Expr' n → Expr' n

embed-expr : ∀ {n} → Expr' n → Expr n
embed-expr (var x)  = Solver.var x
embed-expr (e₁ ⊕ e₂) = embed-expr e₁ Solver.⊕ embed-expr e₂

⟦_⟧' : ∀ {n} → Expr' n → Vec InnerCarrier n → InnerCarrier
⟦ var x ⟧'  ρ = Vec.lookup ρ x
⟦ e₁ ⊕ e₂ ⟧' ρ = ⟦ e₁ ⟧' ρ ∙' ⟦ e₂ ⟧' ρ

lem : ∀ {n} (e : Expr' n) (ρ : Vec InnerCarrier n) → ⟦ embed-expr e ⟧ (lift-env ρ) ≈ ` (⟦ e ⟧' ρ)
lem (var x) ρ = reflexive (lookup-map x `_ ρ)
lem (e ⊕ e₁) ρ = begin
                    ⟦ embed-expr e Solver.⊕ embed-expr e₁ ⟧ (lift-env ρ)
                       ≈⟨ refl ⟩
                    ⟦ embed-expr e ⟧ (lift-env ρ) ∙ ⟦ embed-expr e₁ ⟧ (lift-env ρ)
                       ≈⟨ ∙-cong (lem e ρ) (lem e₁ ρ) ⟩
                    ` (⟦ e ⟧' ρ ∙' ⟦ e₁ ⟧' ρ)
                 ∎
  where open import Relation.Binary.Reasoning.Setoid (setoid)

injective : ∀ {n}(e₁ e₂ : Expr' n)(ρ : Vec (G .CommutativeSemigroup.Carrier) n) →
             ⟦ embed-expr e₁ ⟧ (lift-env ρ) ≈ ⟦ embed-expr e₂ ⟧ (lift-env ρ) →
             ⟦ e₁ ⟧' ρ ≈' ⟦ e₂ ⟧' ρ
injective e₁ e₂ ρ embed-e₁≈embed-e₂ =
  embedding (begin
               ` ⟦ e₁ ⟧' ρ                    ≈⟨ sym (lem e₁ ρ) ⟩
               ⟦ embed-expr e₁ ⟧ (lift-env ρ) ≈⟨ embed-e₁≈embed-e₂ ⟩
               ⟦ embed-expr e₂ ⟧ (lift-env ρ) ≈⟨ lem e₂ ρ ⟩
               ` ⟦ e₂ ⟧' ρ
            ∎)
  where open import Relation.Binary.Reasoning.Setoid (setoid)

prove′ : ∀ {n} (e₁ e₂ : Expr' n) → Maybe (∀ ρ → ⟦ e₁ ⟧' ρ ≈' ⟦ e₂ ⟧' ρ)
prove′ e₁ e₂ =
  Maybe.map lemma (decToMaybe (normalise (embed-expr e₁) ≟ normalise (embed-expr e₂)))
  where
  open PropositionalEquality using (_≡_; cong)
  open PropositionalEquality.≡-Reasoning
  lemma : normalise (embed-expr e₁) ≡ normalise (embed-expr e₂) → ∀ ρ → ⟦ e₁ ⟧' ρ ≈' ⟦ e₂ ⟧' ρ
  lemma eq ρ =
    injective e₁ e₂ ρ
    (R.prove (lift-env ρ) (embed-expr e₁) (embed-expr e₂) (reflexive (begin
       ⟦ normalise (embed-expr e₁) ⟧⇓ (lift-env ρ)  ≡⟨ cong (λ e → ⟦ e ⟧⇓ (lift-env ρ)) eq ⟩
       ⟦ normalise (embed-expr e₂) ⟧⇓ (lift-env ρ)  ∎)))

prove : ∀ n (e₁ e₂ : Expr' n) → From-just (prove′ e₁ e₂)
prove _ e₁ e₂ = from-just (prove′ e₁ e₂)

import Data.Nat.Properties as ℕₚ

v# : ∀ m {n} {m<n : True (suc m ℕₚ.≤? n)} → Expr' n
v# m {n} {m<n} = var ((# m) {n} {m<n})

{-
test : ∀ x y z → (x ∙' y) ∙' z ≈' z ∙' (y ∙' x)
test a b c =
   prove 3 ((x ⊕ y) ⊕ z) (z ⊕ (y ⊕ x)) (a ∷ b ∷ c ∷ [])
  where x = v# 0
        y = v# 1
        z = v# 2
-}
