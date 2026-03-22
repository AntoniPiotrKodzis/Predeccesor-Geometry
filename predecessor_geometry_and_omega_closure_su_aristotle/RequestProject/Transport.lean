/-
# Transport Invariance and Descent

Formalization of Section 2.4–2.5 of the preprint:
- Predecessor-geometry groupoid (Definition 2.6, modeled via the equivalence relation)
- Transport-invariant stage assignments (Definition 2.7)
- Descent along extensional collapse (Proposition 2.10)
-/
import Mathlib
import RequestProject.Basic
import RequestProject.BisimClosure

universe u v

namespace PredStructure

variable (P : PredStructure.{u})

/-! ## Transport-Invariant Stage Assignments (Definition 2.7) -/

/-- A stage assignment `F : A → C` is predecessor-geometry transport invariant
    if `a ≃_Geom b` implies `F(a) = F(b)` (Definition 2.7, simplified to Set-valued).
    In the full version, one would require specified isomorphisms/equivalences;
    here we work with propositional equality as appropriate for set-level carriers. -/
def IsTransportInvariant {C : Type v} (F : P.carrier → C) : Prop :=
  ∀ a b, PredGeomEquiv P P a b → F a = F b

/-! ## Descent along Extensional Collapse (Proposition 2.10) -/

/-- If `F` is transport invariant, it descends to the extensional collapse
    (Proposition 2.10). -/
theorem descent_along_extCollapse {C : Type v} (F : P.carrier → C)
    (hF : P.IsTransportInvariant F) :
    ∃ F_bar : P.ExtCollapse → C, ∀ a, F_bar (P.extCollapseQuot a) = F a := by
  exact ⟨Quotient.lift F hF, fun _ => rfl⟩

/-- The descended function is unique (Proposition 2.10, uniqueness). -/
theorem descent_unique {C : Type v} (F : P.carrier → C)
    (hF : P.IsTransportInvariant F)
    (G₁ G₂ : P.ExtCollapse → C)
    (h₁ : ∀ a, G₁ (P.extCollapseQuot a) = F a)
    (h₂ : ∀ a, G₂ (P.extCollapseQuot a) = F a) :
    G₁ = G₂ := by
  ext x
  induction x using Quotient.ind with
  | _ a =>
    change G₁ (P.extCollapseQuot a) = G₂ (P.extCollapseQuot a)
    rw [h₁, h₂]

end PredStructure
