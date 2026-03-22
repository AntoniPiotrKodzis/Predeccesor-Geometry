/-
# Predecessor Geometry: Basic Definitions

Formalization of Sections 2.1–2.3 of the preprint:
- Predecessor structures (Definition 2.1)
- Initial segments / predecessor sets (Definition 2.2)
- Bounded simulations and bisimulations (Definitions 2.3, 2.4)
- Predecessor-geometry equivalence (Definition 2.5)
- Lemma 2.5: predecessor-geometry equivalence is an equivalence relation
-/
import Mathlib

universe u v

/-! ## Predecessor Structures -/

/-- A predecessor structure is a type equipped with a binary relation `≺`,
    intended to be irreflexive and transitive (Definition 2.1). -/
structure PredStructure where
  carrier : Type u
  prec : carrier → carrier → Prop

namespace PredStructure

variable (P : PredStructure.{u})

/-- The initial segment (predecessor set) of `a` in `P` (Definition 2.2). -/
def PredSet (a : P.carrier) : Set P.carrier :=
  { x | P.prec x a }

/-- The induced predecessor relation on the initial segment of `a`. -/
def PredPrec (a : P.carrier) (x y : P.PredSet a) : Prop :=
  P.prec x.val y.val

/-- The predecessor structure induced on `Pred(a)` (Definition 2.2). -/
def PredSubstructure (a : P.carrier) : PredStructure where
  carrier := P.PredSet a
  prec := P.PredPrec a

end PredStructure

/-! ## Bounded Simulations and Bisimulations -/

/-- A bounded simulation from `a` in `P` to `b` in `Q` is a relation
    `R ⊆ Pred_P(a) × Pred_Q(b)` satisfying the Forth condition (Definition 2.3). -/
structure BoundedSimulation (P Q : PredStructure.{u}) (a : P.carrier) (b : Q.carrier) where
  rel : P.PredSet a → Q.PredSet b → Prop
  forth : ∀ (x : P.PredSet a) (y : Q.PredSet b),
    rel x y →
    ∀ (x' : P.PredSet a), P.prec x'.val x.val →
      ∃ (y' : Q.PredSet b), Q.prec y'.val y.val ∧ rel x' y'

/-- A bounded bisimulation between `a` in `P` and `b` in `Q` is a relation
    `R ⊆ Pred_P(a) × Pred_Q(b)` such that both `R` and `R^op` satisfy Forth
    (Definition 2.4). -/
structure BoundedBisimulation (P Q : PredStructure.{u}) (a : P.carrier) (b : Q.carrier) where
  rel : P.PredSet a → Q.PredSet b → Prop
  forth : ∀ (x : P.PredSet a) (y : Q.PredSet b),
    rel x y →
    ∀ (x' : P.PredSet a), P.prec x'.val x.val →
      ∃ (y' : Q.PredSet b), Q.prec y'.val y.val ∧ rel x' y'
  back : ∀ (x : P.PredSet a) (y : Q.PredSet b),
    rel x y →
    ∀ (y' : Q.PredSet b), Q.prec y'.val y.val →
      ∃ (x' : P.PredSet a), P.prec x'.val x.val ∧ rel x' y'

/-- Predecessor-geometry equivalence: `a ≃_Geom b` iff there exists a bounded
    bisimulation between the initial segments of `a` and `b` (Definition 2.5). -/
def PredGeomEquiv (P Q : PredStructure.{u}) (a : P.carrier) (b : Q.carrier) : Prop :=
  Nonempty (BoundedBisimulation P Q a b)

/-! ## Lemma 2.5: PredGeomEquiv is an equivalence relation -/

/-- The diagonal relation on `Pred(a)` is a bounded bisimulation from `a` to `a`
    (reflexivity witness). -/
def BoundedBisimulation.refl (P : PredStructure.{u}) (a : P.carrier) :
    BoundedBisimulation P P a a where
  rel x y := x.val = y.val
  forth x y hxy x' hx'x := by
    refine ⟨⟨x'.val, x'.prop⟩, ?_, rfl⟩
    rw [← hxy]; exact hx'x
  back x y hxy y' hy'y := by
    refine ⟨⟨y'.val, y'.prop⟩, ?_, rfl⟩
    rw [hxy]; exact hy'y

/-- The converse of a bounded bisimulation is a bounded bisimulation (symmetry witness). -/
def BoundedBisimulation.symm {P Q : PredStructure.{u}} {a : P.carrier} {b : Q.carrier}
    (B : BoundedBisimulation P Q a b) : BoundedBisimulation Q P b a where
  rel y x := B.rel x y
  forth y x hyx y' hy'y := B.back x y hyx y' hy'y
  back y x hyx x' hx'x := B.forth x y hyx x' hx'x

/-- The relational composition of bounded bisimulations is a bounded bisimulation
    (transitivity witness). -/
def BoundedBisimulation.trans {P Q R : PredStructure.{u}}
    {a : P.carrier} {b : Q.carrier} {c : R.carrier}
    (B₁ : BoundedBisimulation P Q a b) (B₂ : BoundedBisimulation Q R b c) :
    BoundedBisimulation P R a c where
  rel x z := ∃ (y : Q.PredSet b), B₁.rel x y ∧ B₂.rel y z
  forth x z hxz x' hx'x := by
    obtain ⟨y, h1, h2⟩ := hxz
    obtain ⟨y', hy'y, h1'⟩ := B₁.forth x y h1 x' hx'x
    obtain ⟨z', hz'z, h2'⟩ := B₂.forth y z h2 y' hy'y
    exact ⟨z', hz'z, y', h1', h2'⟩
  back x z hxz z' hz'z := by
    obtain ⟨y, h1, h2⟩ := hxz
    obtain ⟨y', hy'y, h2'⟩ := B₂.back y z h2 z' hz'z
    obtain ⟨x', hx'x, h1'⟩ := B₁.back x y h1 y' hy'y
    exact ⟨x', hx'x, y', h1', h2'⟩

/-- Predecessor-geometry equivalence is reflexive (Lemma 2.5). -/
theorem PredGeomEquiv.refl (P : PredStructure.{u}) (a : P.carrier) :
    PredGeomEquiv P P a a :=
  ⟨BoundedBisimulation.refl P a⟩

/-- Predecessor-geometry equivalence is symmetric (Lemma 2.5). -/
theorem PredGeomEquiv.symm {P Q : PredStructure.{u}} {a : P.carrier} {b : Q.carrier}
    (h : PredGeomEquiv P Q a b) : PredGeomEquiv Q P b a := by
  obtain ⟨B⟩ := h
  exact ⟨B.symm⟩

/-- Predecessor-geometry equivalence is transitive (Lemma 2.5). -/
theorem PredGeomEquiv.trans {P Q R : PredStructure.{u}}
    {a : P.carrier} {b : Q.carrier} {c : R.carrier}
    (h₁ : PredGeomEquiv P Q a b) (h₂ : PredGeomEquiv Q R b c) :
    PredGeomEquiv P R a c := by
  obtain ⟨B₁⟩ := h₁
  obtain ⟨B₂⟩ := h₂
  exact ⟨B₁.trans B₂⟩

/-- Within a single predecessor structure, predecessor-geometry equivalence is
    an equivalence relation on indices (Lemma 2.5). -/
theorem predGeomEquiv_equivalence (P : PredStructure.{u}) :
    Equivalence (PredGeomEquiv P P) where
  refl := PredGeomEquiv.refl P
  symm := PredGeomEquiv.symm
  trans := PredGeomEquiv.trans
