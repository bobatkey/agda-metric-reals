{-# OPTIONS --without-K --allow-unsolved-metas #-}

module MetricSpace.CauchyReals where

open import Level using (0β)
open import MetricSpace
open import MetricSpace.Category
open import MetricSpace.Completion renaming (map to π-map; unit to π-unit; map-cong to π-map-cong; map-β to π-map-β; map-id to π-map-id)
open import MetricSpace.Rationals
open import MetricSpace.MonoidalProduct
open import MetricSpace.Terminal
open import MetricSpace.Scaling
open import Data.Rational.Unnormalised.Positive as ββΊ using (ββΊ)
open import Algebra
open import Data.Product using (_,_; Ξ£-syntax)
open import Data.Rational.Unnormalised as β using () renaming (βα΅ to β)
import Data.Rational.Unnormalised.Properties as β
open import Data.Sum using (_β_; injβ; injβ)
open import Data.Unit using (tt)
open import Data.Real.UpperClosed as βα΅ using (βα΅)
open import Relation.Nullary
open import Relation.Binary using (IsEquivalence; Setoid)
--open import Relation.Binary using (tri<; triβ; tri>)


------------------------------------------------------------------------------
-- the real numbers as the metric completion of the rationals

βspc : MSpc
βspc = π βspc

βspc[_] : ββΊ β MSpc
βspc[ b ] = π βspc[ b ]

βspc[_β© : ββΊ β MSpc
βspc[ a β© = π βspc[ a β©

β : Set
β = βspc .MSpc.Carrier

β[_] : ββΊ β Set
β[ q ] = βspc[ q ] .MSpc.Carrier

------------------------------------------------------------------------------

_β_ : β β β β Set
x β y = MSpc._β_ βspc x y

β-refl : β {x} β x β x
β-refl {x} = MSpc.β-refl βspc {x}

β-sym : β {x y} β x β y β y β x
β-sym {x}{y} = MSpc.β-sym βspc {x} {y}

β-trans : β {x y z} β x β y β y β z β x β z
β-trans {x}{y}{z} = MSpc.β-trans βspc {x} {y} {z}

β-isEquivalence : IsEquivalence _β_
β-isEquivalence .IsEquivalence.refl {x} = β-refl {x}
β-isEquivalence .IsEquivalence.sym {x} {y} = β-sym {x} {y}
β-isEquivalence .IsEquivalence.trans {x} {y} {z} = β-trans {x} {y} {z}

β-setoid : Setoid 0β 0β
β-setoid .Setoid.Carrier = β
β-setoid .Setoid._β_ = _β_
β-setoid .Setoid.isEquivalence = β-isEquivalence

------------------------------------------------------------------------------
-- Arithmetic as morphisms in Metric Spaces

-- FIXME: this seems to type check really slowly without no-eta-equality on MSpc and _β_
addβ : (βspc β βspc) β βspc
addβ = π-map add β monoidal-β

negateβ : βspc β βspc
negateβ = π-map negate

zeroβ : β€β β βspc
zeroβ = π-unit β zero

-- FIXME: now to prove that this gives an abelian group. This is true
-- for any monoid + monoidal functor, and should probably rely on
-- results from the agda-categories library. AFAICT (2021-12-01) I
-- don't think this result is in the agda-categories library.
addβ-comm : (addβ β β-symmetry) βf addβ
addβ-comm =
  begin
    addβ β β-symmetry
  β‘β¨β©
    (π-map add β monoidal-β) β β-symmetry
  βΛβ¨ assoc (π-map add) monoidal-β β-symmetry β©
    π-map add β (monoidal-β β β-symmetry)
  ββ¨ β-cong (βf-isEquivalence .IsEquivalence.refl) monoidal-symmetry β©
    π-map add β (π-map β-symmetry β monoidal-β)
  ββ¨ assoc (π-map add) (π-map β-symmetry) monoidal-β  β©
    (π-map add β π-map β-symmetry) β monoidal-β
  βΛβ¨ β-cong π-map-β (βf-isEquivalence .IsEquivalence.refl) β©
    π-map (add β β-symmetry) β monoidal-β
  ββ¨ β-cong (π-map-cong add-comm) (βf-isEquivalence .IsEquivalence.refl) β©
    π-map add β monoidal-β
  β‘β¨β©
    addβ
  β
  where open import Relation.Binary.Reasoning.Setoid βf-setoid
        open import Relation.Binary using (IsEquivalence; Setoid)

addβ-assoc : (addβ β (addβ βf id) β β-assoc) βf (addβ β (id βf addβ))
addβ-assoc =
  begin
    addβ β (addβ βf id) β β-assoc
  β‘β¨β©
    (π-map add β monoidal-β) β ((π-map add β monoidal-β) βf id) β β-assoc
  βΛβ¨ β-cong refl (β-cong (βf-cong refl (identityΛ‘ id)) refl) β©
    (π-map add β monoidal-β) β ((π-map add β monoidal-β) βf (id β id)) β β-assoc
  βΛβ¨ β-cong refl (β-cong (βf-cong refl (β-cong π-map-id refl)) refl) β©
    (π-map add β monoidal-β) β ((π-map add β monoidal-β) βf (π-map id β id)) β β-assoc
  ββ¨ β-cong refl (β-cong (βf-β (π-map add) monoidal-β (π-map id) id) refl) β©
    (π-map add β monoidal-β) β ((π-map add βf π-map id) β (monoidal-β βf id)) β β-assoc
  ββ¨ assoc (π-map add β monoidal-β) ((π-map add βf π-map id) β (monoidal-β βf id)) β-assoc β©
    ((π-map add β monoidal-β) β (π-map add βf π-map id) β (monoidal-β βf id)) β β-assoc
  ββ¨ β-cong (assoc _ _ _) refl β©
    (((π-map add β monoidal-β) β (π-map add βf π-map id)) β (monoidal-β βf id)) β β-assoc
  βΛβ¨ β-cong (β-cong (assoc _ _ _) refl) refl β©
    ((π-map add β monoidal-β β (π-map add βf π-map id)) β (monoidal-β βf id)) β β-assoc
  ββ¨ β-cong (β-cong (β-cong refl (monoidal-natural add id)) refl) refl β©
    ((π-map add β π-map (add βf id) β monoidal-β) β (monoidal-β βf id)) β β-assoc
  ββ¨ β-cong (β-cong (assoc _ _ _) refl) refl β©
    (((π-map add β π-map (add βf id)) β monoidal-β) β (monoidal-β βf id)) β β-assoc
  ββ¨ β-cong (sym (assoc _ _ _)) refl β©
    ((π-map add β π-map (add βf id)) β monoidal-β β (monoidal-β βf id)) β β-assoc
  ββ¨ sym (assoc _ _ _) β©
    (π-map add β π-map (add βf id)) β (monoidal-β β (monoidal-β βf id)) β β-assoc
  ββ¨ β-cong (sym π-map-β) (sym (assoc _ _ _)) β©
    π-map (add β (add βf id)) β (monoidal-β β (monoidal-β βf id) β β-assoc)
  ββ¨ β-cong refl monoidal-assoc β©
    π-map (add β (add βf id)) β π-map β-assoc β monoidal-β β (id βf monoidal-β)
  ββ¨ assoc _ _ _ β©
    (π-map (add β (add βf id)) β π-map β-assoc) β monoidal-β β (id βf monoidal-β)
  ββ¨ β-cong (sym π-map-β) refl β©
    π-map ((add β (add βf id)) β β-assoc) β monoidal-β β (id βf monoidal-β)
  ββ¨ β-cong (π-map-cong (sym (assoc _ _ _))) refl β©
    π-map (add β (add βf id) β β-assoc) β monoidal-β β (id βf monoidal-β)
  ββ¨ β-cong (π-map-cong add-assoc) refl β©
    π-map (add β (id βf add)) β monoidal-β β (id βf monoidal-β)
  ββ¨ β-cong π-map-β refl β©
    (π-map add β π-map (id βf add)) β monoidal-β β (id βf monoidal-β)
  ββ¨ assoc _ _ _ β©
    ((π-map add β π-map (id βf add)) β monoidal-β) β (id βf monoidal-β)
  ββ¨ β-cong (sym (assoc _ _ _)) refl β©
    (π-map add β π-map (id βf add) β monoidal-β) β (id βf monoidal-β)
  ββ¨ β-cong (β-cong refl (sym (monoidal-natural id add))) refl β©
    (π-map add β monoidal-β β (π-map id βf π-map add)) β (id βf monoidal-β)
  ββ¨ β-cong (assoc _ _ _) refl β©
    ((π-map add β monoidal-β) β (π-map id βf π-map add)) β (id βf monoidal-β)
  ββ¨ sym (assoc _ _ _) β©
    (π-map add β monoidal-β) β (π-map id βf π-map add) β (id βf monoidal-β)
  ββ¨ β-cong refl (sym (βf-β (π-map id) id (π-map add) monoidal-β)) β©
    (π-map add β monoidal-β) β ((π-map id β id) βf (π-map add β monoidal-β))
  ββ¨ β-cong refl (βf-cong (β-cong π-map-id refl) refl) β©
    (π-map add β monoidal-β) β ((id β id) βf (π-map add β monoidal-β))
  ββ¨ β-cong refl (βf-cong (identityΛ‘ id) refl) β©
    (π-map add β monoidal-β) β (id βf (π-map add β monoidal-β))
  β‘β¨β©
    addβ β (id βf addβ)
  β
  where open import Relation.Binary.Reasoning.Setoid βf-setoid
        open import Relation.Binary using (IsEquivalence; Setoid)
        refl : β {X Y} {f : X β Y} β f βf f
        refl = βf-isEquivalence .IsEquivalence.refl
        sym : β {X Y} {f g : X β Y} β f βf g β g βf f
        sym = βf-isEquivalence .IsEquivalence.sym

-- This proof is very simple, but very long!
addβ-identityΛ‘ : (addβ β (zeroβ βf id) β left-unitβ»ΒΉ) βf id
addβ-identityΛ‘ =
  begin
    addβ β (zeroβ βf id) β left-unitβ»ΒΉ
  β‘β¨β©
    (π-map add β monoidal-β) β ((π-unit β zero) βf id) β left-unitβ»ΒΉ
  ββ¨ β-cong refl (β-cong (βf-cong unit-natural refl) refl) β©
    (π-map add β monoidal-β) β ((π-map zero β π-unit) βf id) β left-unitβ»ΒΉ
  βΛβ¨ β-cong refl (β-cong (βf-cong refl (identityΛ‘ id)) refl) β©
    (π-map add β monoidal-β) β ((π-map zero β π-unit) βf (id β id)) β left-unitβ»ΒΉ
  βΛβ¨ β-cong refl (β-cong (βf-cong refl (β-cong π-map-id refl)) refl) β©
    (π-map add β monoidal-β) β ((π-map zero β π-unit) βf (π-map id β id)) β left-unitβ»ΒΉ
  ββ¨ β-cong refl (β-cong (βf-β (π-map zero) π-unit (π-map id) id) refl) β©
    (π-map add β monoidal-β) β ((π-map zero βf π-map id) β (π-unit βf id)) β left-unitβ»ΒΉ
  ββ¨ assoc (π-map add β monoidal-β) ((π-map zero βf π-map id) β (π-unit βf id)) left-unitβ»ΒΉ β©
    ((π-map add β monoidal-β) β (π-map zero βf π-map id) β (π-unit βf id)) β left-unitβ»ΒΉ
  ββ¨ β-cong (assoc (π-map add β monoidal-β) (π-map zero βf π-map id) (π-unit βf id)) refl β©
    (((π-map add β monoidal-β) β (π-map zero βf π-map id)) β (π-unit βf id)) β left-unitβ»ΒΉ
  βΛβ¨ β-cong (β-cong (assoc (π-map add) monoidal-β (π-map zero βf π-map id)) refl) refl β©
    ((π-map add β monoidal-β β (π-map zero βf π-map id)) β (π-unit βf id)) β left-unitβ»ΒΉ
  ββ¨ β-cong (β-cong (β-cong refl (monoidal-natural zero id)) refl) refl β©
    ((π-map add β π-map (zero βf id) β monoidal-β) β (π-unit βf id)) β left-unitβ»ΒΉ
  ββ¨ β-cong (β-cong (assoc (π-map add) (π-map (zero βf id)) monoidal-β) refl) refl β©
    (((π-map add β π-map (zero βf id)) β monoidal-β) β (π-unit βf id)) β left-unitβ»ΒΉ
  βΛβ¨ β-cong (β-cong (β-cong π-map-β refl) refl) refl β©
    ((π-map (add β (zero βf id)) β monoidal-β) β (π-unit βf id)) β left-unitβ»ΒΉ
  βΛβ¨ β-cong (assoc (π-map (add β (zero βf id))) monoidal-β (π-unit βf id)) refl β©
    (π-map (add β (zero βf id)) β monoidal-β β (π-unit βf id)) β left-unitβ»ΒΉ
  ββ¨ β-cong (β-cong refl monoidal-left-unit) refl β©
    (π-map (add β (zero βf id)) β π-map left-unitβ»ΒΉ β left-unit) β left-unitβ»ΒΉ
  ββ¨ β-cong (assoc (π-map (add β (zero βf id))) (π-map left-unitβ»ΒΉ) left-unit) refl β©
    ((π-map (add β (zero βf id)) β π-map left-unitβ»ΒΉ) β left-unit) β left-unitβ»ΒΉ
  βΛβ¨ β-cong (β-cong π-map-β refl) refl β©
    (π-map ((add β (zero βf id)) β left-unitβ»ΒΉ) β left-unit) β left-unitβ»ΒΉ
  βΛβ¨ assoc (π-map ((add β (zero βf id)) β left-unitβ»ΒΉ)) left-unit left-unitβ»ΒΉ β©
    π-map ((add β (zero βf id)) β left-unitβ»ΒΉ) β left-unit β left-unitβ»ΒΉ
  ββ¨ β-cong (π-map-cong (sym (assoc add (zero βf id) left-unitβ»ΒΉ))) left-unit-isoβ β©
    π-map (add β (zero βf id) β left-unitβ»ΒΉ) β id
  ββ¨ β-cong (π-map-cong add-identityΛ‘) refl β©
    π-map id β id
  ββ¨ β-cong π-map-id refl β©
    id β id
  ββ¨ identityΛ‘ id β©
    id
  β
  where open import Relation.Binary.Reasoning.Setoid βf-setoid
        open import Relation.Binary using (IsEquivalence; Setoid)
        refl : β {X Y} {f : X β Y} β f βf f
        refl = βf-isEquivalence .IsEquivalence.refl
        sym : β {X Y} {f g : X β Y} β f βf g β g βf f
        sym = βf-isEquivalence .IsEquivalence.sym

addβ-inverse : (addβ β (id βf negateβ) β (derelict βf derelict) β duplicate) βf (zeroβ β discard)
addβ-inverse =
  begin
    addβ β (id βf negateβ) β (derelict βf derelict) β duplicate
  β‘β¨β©
    (π-map add β monoidal-β) β (id βf π-map negate) β (derelict βf derelict) β duplicate
  ββ¨ β-cong refl (β-cong (βf-cong (sym π-map-id) refl) refl) β©
    (π-map add β monoidal-β) β (π-map id βf π-map negate) β (derelict βf derelict) β duplicate
  ββ¨ assoc _ _ _ β©
    ((π-map add β monoidal-β) β (π-map id βf π-map negate)) β (derelict βf derelict) β duplicate
  ββ¨ β-cong (sym (assoc _ _ _)) refl β©
    (π-map add β monoidal-β β (π-map id βf π-map negate)) β (derelict βf derelict) β duplicate
  ββ¨ β-cong (β-cong refl (monoidal-natural id negate)) refl β©
    (π-map add β π-map (id βf negate) β monoidal-β) β (derelict βf derelict) β duplicate
  ββ¨ {!!} β© -- FIXME: need to prove more properties of ![_] and its interaction with π
    zeroβ β discard
  β
  where open import Relation.Binary.Reasoning.Setoid βf-setoid
        open import Relation.Binary using (IsEquivalence; Setoid)
        refl : β {X Y} {f : X β Y} β f βf f
        refl = βf-isEquivalence .IsEquivalence.refl
        sym : β {X Y} {f g : X β Y} β f βf g β g βf f
        sym = βf-isEquivalence .IsEquivalence.sym


------------------------------------------------------------------------------
-- Arithmetic operations as plain functions

-- FIXME: rename these to remove the β suffixes

βββ : β β β
βββ q = π-unit ._β_.fun q

_+β_ : β β β β β
x +β y = addβ ._β_.fun (x , y)

-β_ : β β β
-β_ x = negateβ ._β_.fun x

0β : β
0β = zeroβ ._β_.fun tt

_-β_ : β β β β β
x -β y = x +β (-β y)

------------------------------------------------------------------------------
-- Properties of _+_ and -_

+β-cong : Congruentβ _β_ _+β_ -- β {xβ xβ yβ yβ} β xβ β xβ β yβ β yβ β (xβ +β yβ) β (xβ +β yβ)
+β-cong {xβ}{xβ}{yβ}{yβ} xββxβ yββyβ =
  _β_.cong addβ {xβ , yβ} {xβ , yβ}
                 (β-β {βspc}{βspc} {xβ}{xβ}{yβ}{yβ} xββxβ yββyβ)

-β-cong : Congruentβ _β_ (-β_)
-β-cong {xβ}{xβ} xββxβ =
  _β_.cong negateβ {xβ} {xβ} xββxβ

+β-assoc : β x y z β ((x +β y) +β z) β (x +β (y +β z))
+β-assoc x y z = addβ-assoc ._βf_.fβf (x , (y , z))

+β-comm : β x y β (x +β y) β (y +β x)
+β-comm x y = addβ-comm ._βf_.fβf (y , x)

+β-identityΛ‘ : β x β (0β +β x) β x
+β-identityΛ‘ x = addβ-identityΛ‘ ._βf_.fβf x

+β-identityΚ³ : β x β (x +β 0β) β x
+β-identityΚ³ x =
  begin
    x +β 0β
  ββ¨ +β-comm x 0β β©
    0β +β x
  ββ¨ +β-identityΛ‘ x β©
    x
  β
  where open import Relation.Binary.Reasoning.Setoid β-setoid

+-identity : Identity _β_ 0β _+β_
+-identity = +β-identityΛ‘ , +β-identityΚ³

+-inverseΚ³ : RightInverse _β_ 0β -β_ _+β_
+-inverseΚ³ x = addβ-inverse ._βf_.fβf x

+-inverseΛ‘ : LeftInverse _β_ 0β -β_ _+β_
+-inverseΛ‘ x =
  begin
    (-β x) +β x  ββ¨ +β-comm (-β x) x β©
    x +β (-β x)  ββ¨ +-inverseΚ³ x β©
    0β           β
  where open import Relation.Binary.Reasoning.Setoid β-setoid

+-inverse : Inverse _β_ 0β -β_ _+β_
+-inverse = +-inverseΛ‘ , +-inverseΚ³

------------------------------------------------------------------------------
-- Packaging up the proofs of algeraic properties

+-isMagma : IsMagma _β_ _+β_
+-isMagma = record { isEquivalence = β-isEquivalence ; β-cong = Ξ» {xβ}{xβ}{yβ}{yβ} β +β-cong {xβ}{xβ}{yβ}{yβ} }

+-isSemigroup : IsSemigroup _β_ _+β_
+-isSemigroup = record { isMagma = +-isMagma ; assoc = +β-assoc }

+-isCommutativeSemigroup : IsCommutativeSemigroup _β_ _+β_
+-isCommutativeSemigroup = record { isSemigroup = +-isSemigroup ; comm = +β-comm }

+-0-isMonoid : IsMonoid _β_ _+β_ 0β
+-0-isMonoid = record { isSemigroup = +-isSemigroup ; identity = +-identity }

+-0-isCommutativeMonoid : IsCommutativeMonoid _β_ _+β_ 0β
+-0-isCommutativeMonoid = record { isMonoid = +-0-isMonoid ; comm = +β-comm }

+-0-isGroup : IsGroup _β_ _+β_ 0β (-β_)
+-0-isGroup = record { isMonoid = +-0-isMonoid ; inverse = +-inverse ; β»ΒΉ-cong = Ξ» {xβ}{xβ} β -β-cong {xβ}{xβ} }

+-0-isAbelianGroup : IsAbelianGroup _β_ _+β_ 0β (-β_)
+-0-isAbelianGroup = record { isGroup = +-0-isGroup ; comm = +β-comm }

+-0-AbelianGroup : AbelianGroup 0β 0β
+-0-AbelianGroup = record { isAbelianGroup = +-0-isAbelianGroup }

-- FIXME: bundles



------------------------------------------------------------------------------
-- Order and apartness

-- FIXME: this is unfinished

module _ where

  open RegFun

  0β€β : β β Set
  0β€β x = β Ξ΅ β β.- ββΊ.fog Ξ΅ β.β€ x .RegFun.rfun Ξ΅

  -- https://github.com/coq-community/corn/blob/master/reals/fast/CRGroupOps.v#L177
  -- 0β€β-cong : β {x y} β x β y β 0β€β x β 0β€β y
  -- 0β€β-cong {x} {y} xβy 0β€x Ξ΅ = {!!}

  --     with β.<-cmp (x .rfun Ξ΅) (y .rfun Ξ΅)
  -- ... | tri< xβ¨Ξ΅β©<yβ¨Ξ΅β© _ _ =
  --   begin
  --     β.- ββΊ.fog Ξ΅
  --   β€β¨ 0β€x Ξ΅ β©
  --     x .rfun Ξ΅
  --   <β¨ xβ¨Ξ΅β©<yβ¨Ξ΅β© β©
  --     y .rfun Ξ΅
  --   β
  --   where open β.β€-Reasoning
  -- ... | triβ _ xβ¨Ξ΅β©βyβ¨Ξ΅β© _ =
  --   begin
  --     β.- ββΊ.fog Ξ΅
  --   β€β¨ 0β€x Ξ΅ β©
  --     x .rfun Ξ΅
  --   ββ¨ xβ¨Ξ΅β©βyβ¨Ξ΅β© β©
  --     y .rfun Ξ΅
  --   β
  --   where open β.β€-Reasoning
  -- ... | tri> _ _ yβ¨Ξ΅β©<xβ¨Ξ΅β© =
  --   begin
  --     β.- ββΊ.fog Ξ΅
  --   β€β¨ {!!} β©
  --     y .rfun Ξ΅
  --   β
  --   where open β.β€-Reasoning

  -- -Ξ΅ β€ xβ¨Ξ΅β©
  -- | yΞ΅ - xΞ΅ | β€ 2Ξ΅
  -- yΞ΅ < xΞ΅
  -- ==> xΞ΅ - yΞ΅ β€ 2Ξ΅
  -- ==> xΞ΅ - 2Ξ΅ β€ yΞ΅
  --

  -- β-π {βspc} {x}{y} xβy Ξ΅ Ξ΅ :  difference between x(Ξ΅) and y(Ξ΅) is less than (Ξ΅ + Ξ΅)
  -- otherwise, x .rfun Ξ΅ + (Ξ΅ + Ξ΅) β€ y .rfun Ξ΅
  -- so Ξ΅ β€ y .rfun Ξ΅ and so - Ξ΅ β€ y .rfun Ξ΅

-- βNot greater thanβ
_β€β_ : β β β β Set
x β€β y = 0β€β (y -β x)

β€β-refl : β x β x β€β x
β€β-refl x Ξ΅ = {!!}

0<β : β β Set
0<β x = Ξ£[ Ξ΅ β ββΊ ] (π-unit ._β_.fun (ββΊ.fog Ξ΅) β€β x )

-- βGreater thanβ
_<β_ : β β β β Set
x <β y = 0<β (y -β x)

-- Apartness
_#β_ : β β β β Set
x #β y = x <β y β y <β x

-- FIXME: axioms for apartness

-- FIXME: prove that the distance function on the reals is really the
-- absolute value of the difference. This would require a mapping of
-- the metric space reals into the upper reals.

{-
module _ where

  open import upper-reals
  open upper-reals.βα΅

  to-upper-real : β β βα΅
  to-upper-real x .contains q = {!x β€β (βββ q)!}
  to-upper-real x .upper = {!!}
  to-upper-real x .closed = {!!}
-}

------------------------------------------------------------------------------
-- Multiplication and reciprocal

-- scaling a real by a positive rational
scale : β q β ![ q ] βspc β βspc
scale q = π-map (β-scale q) β distr q

-- Fully "metrised" versions of multiplication and reciprocal

mulβ : β a b β (![ b ] βspc[ a ] β ![ a ] βspc[ b ]) β βspc[ a ββΊ.* b ]
mulβ a b = π-map (mul a b) β monoidal-β β (distr b βf distr a)

reciprocalβ : β a β ![ ββΊ.1/ (a ββΊ.* a) ] βspc[ a β© β βspc
reciprocalβ a = π-map (recip a) β distr (ββΊ.1/ (a ββΊ.* a))

------------------------------------------------------------------------------
-- Bounding regular functions

open import Data.Product
import Data.Rational.Unnormalised as β
import Data.Rational.Unnormalised.Properties as β

module _ where
  import Data.Integer as β€
  import Data.Nat as β

  0<Β½ : β.0βα΅ β.< β.Β½
  0<Β½ = β.*<* (β€.+<+ (β.sβ€s β.zβ€n))

get-bound : β β ββΊ
get-bound r =
  ββΊ.β¨ (β.β£ r .RegFun.rfun ββΊ.Β½ β£ β.+ β.Β½)
     , β.positive
        (begin-strict
           β.0βα΅
         β€β¨ β.0β€β£pβ£ (r .RegFun.rfun ββΊ.Β½) β©
           β.β£ r .RegFun.rfun ββΊ.Β½ β£
         ββ¨ β.β-sym (β.+-identityΚ³ β.β£ r .RegFun.rfun ββΊ.Β½ β£) β©
           β.β£ r .RegFun.rfun ββΊ.Β½ β£ β.+ β.0βα΅
         <β¨ β.+-mono-β€-< (β.β€-refl {β.β£ r .RegFun.rfun ββΊ.Β½ β£}) 0<Β½ β©
           β.β£ r .RegFun.rfun ββΊ.Β½ β£ β.+ β.Β½
         β)
     β©
  where open β.β€-Reasoning

bound : β β Ξ£[ q β ββΊ ] β[ q ]
bound r .projβ = get-bound r
bound r .projβ = {!!} -- π-map (clamping.clamp (get-bound r)) ._β_.fun r

open _β_

β-unbound : β {q} β β[ q ] β β
β-unbound {q} = π-map (unbound q) .fun

bound-eq : β x β β-unbound (bound x .projβ) β x
bound-eq x =
  π-β {x = β-unbound (bound x .projβ)} {y = x} Ξ» Ξ΅β Ξ΅β β
  begin
     βα΅.rational β.β£ β-unbound (bound x .projβ) .RegFun.rfun Ξ΅β β.- x .RegFun.rfun Ξ΅β β£
  β‘β¨β©
     βα΅.rational β.β£ clamping.clamp-v (get-bound x) (x .RegFun.rfun Ξ΅β) β.- x .RegFun.rfun Ξ΅β β£
  β€β¨ {!!} β©
     βα΅.rational+ (Ξ΅β ββΊ.+ Ξ΅β)
  β
  where open βα΅.β€-Reasoning

_*β_ : β β β β β
_*β_ x y =
  let a , x' = bound x in
  let b , y' = bound y in
  β-unbound (mulβ a b .fun (x' , y'))

-- TODO:
-- 1. congruence
-- 2. associativity (needs proofs from rationals)
-- 3. distributivity
-- 4. identities
-- 5. zeros

2β : β
2β = βββ (β.1βα΅ β.+ β.1βα΅)

4β : β
4β = 2β *β 2β

4β : β
4β = β.1βα΅ β.+ β.1βα΅ β.+ β.1βα΅ β.+ β.1βα΅

module _ where
  open import Relation.Binary.PropositionalEquality using (_β‘_; refl)

  _ :  4β .RegFun.rfun ββΊ.Β½ β‘ 4β
  _ = refl

------------------------------------------------------------------------
-- TODO: reciprocal

{- If a real is greater than 0 by the above definition, then we can
   use the Ξ΅ from that to bound it from underneath. Then apply the
   reciprocal on the rationals. -}

------------------------------------------------------------------------
-- TODO: Alternating decreasing series

-- If we have:
--    a series      a : β β β
--    limit is 0:   β Ξ΅ β Ξ£[ n β β ] (β£ a n β£ β€ Ξ΅)
--    alternating:  ???
--    decreasing:   β i β β£ a (suc i) β£ < β£ a i β£

-- define x(Ξ΅) = sum(modulus(Ξ΅), a)
--   then prove that this is a regular function

-- and then prove that it gives us the infinite sum??
