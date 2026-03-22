/-
# Bisimulation Closure and Extensional Collapse

Formalization of Appendix material and Theorem 8.3 of the preprint:
- Global bisimulation (used in Theorem 8.3)
- Extensional collapse as set-quotient (Theorem 8.3, parts E1–E3)
- Universal property of the extensional collapse
-/
import Mathlib
import RequestProject.Basic

universe u

namespace PredStructure

variable (P : PredStructure.{u})

/-! ## Global Bisimulation -/

/-- A global bisimulation on `(X, ≺)` is a relation `R` satisfying forth and back
    for all related pairs (as in the proof of Theorem 8.3). -/
structure GlobalBisimulation where
  rel : P.carrier → P.carrier → Prop
  forth : ∀ u v, rel u v → ∀ u', P.prec u' u → ∃ v', P.prec v' v ∧ rel u' v'
  back  : ∀ u v, rel u v → ∀ v', P.prec v' v → ∃ u', P.prec u' u ∧ rel u' v'

/-- Two elements are globally bisimilar if there exists a global bisimulation
    relating them. -/
def GlobalBisimilar (x y : P.carrier) : Prop :=
  ∃ B : P.GlobalBisimulation, B.rel x y

/-! ## Forward direction: global → bounded (Theorem 8.3 E2, ⇒) -/

/-- If elements are related by a global bisimulation, then they have the same
    predecessor geometry. The restriction of a global bisimulation to initial
    segments gives a bounded bisimulation (Theorem 8.3, E2, ⇒ direction). -/
theorem globalBisimilar_implies_predGeomEquiv
    (hTrans : ∀ a b c : P.carrier, P.prec a b → P.prec b c → P.prec a c)
    {x y : P.carrier} (h : P.GlobalBisimilar x y) :
    PredGeomEquiv P P x y := by
  obtain ⟨B, hxy⟩ := h
  refine ⟨⟨fun a b => B.rel a.val b.val, ?_, ?_⟩⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ hab ⟨a', ha'⟩ hprec
    obtain ⟨b', hb'b, hab'⟩ := B.forth a b hab a' hprec
    exact ⟨⟨b', hTrans b' b y hb'b hb⟩, hb'b, hab'⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ hab ⟨b', hb'⟩ hprec
    obtain ⟨a', ha'a, hab'⟩ := B.back a b hab b' hprec
    exact ⟨⟨a', hTrans a' a x ha'a ha⟩, ha'a, hab'⟩

/-! ## Extensional Collapse (Theorem 8.3) -/

/-- The extensional collapse of a predecessor structure is the set-quotient
    by predecessor-geometry equivalence (Theorem 8.3, E1). -/
def ExtCollapse : Type u :=
  Quotient (Setoid.mk (PredGeomEquiv P P) (predGeomEquiv_equivalence P))

/-- The quotient map `q : X → Ec(X)` (Theorem 8.3). -/
def extCollapseQuot : P.carrier → P.ExtCollapse :=
  Quotient.mk (Setoid.mk (PredGeomEquiv P P) (predGeomEquiv_equivalence P))

/-- `q(x) = q(y)` iff `x ≃_Geom y` (Theorem 8.3, E1). -/
theorem extCollapse_eq_iff (x y : P.carrier) :
    P.extCollapseQuot x = P.extCollapseQuot y ↔ PredGeomEquiv P P x y := by
  simp only [extCollapseQuot]
  exact Quotient.eq (r := Setoid.mk (PredGeomEquiv P P) (predGeomEquiv_equivalence P))

/-- Universal property of the extensional collapse: any predecessor-geometry
    invariant function factors uniquely through `q` (Theorem 8.3, E3). -/
theorem extCollapse_lift {Y : Type u} (f : P.carrier → Y)
    (hf : ∀ x y, PredGeomEquiv P P x y → f x = f y) :
    ∃! g : P.ExtCollapse → Y, g ∘ P.extCollapseQuot = f := by
  refine ⟨Quotient.lift f hf, ?_, ?_⟩
  · ext x; rfl
  · intro g hg
    ext ⟨x⟩
    exact congr_fun hg x

end PredStructure
