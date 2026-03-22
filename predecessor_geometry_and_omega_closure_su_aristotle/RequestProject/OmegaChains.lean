/-
# ω-Chains and Cofinal Equivalence

Formalization of Section 5 of the preprint:
- Strict ω-chains (Definition 5.1)
- Cofinal refinement (Definition 5.2)
- Cofinal (bisimulation) equivalence of chains (Definition 5.3)
-/
import Mathlib
import RequestProject.Basic

universe u

namespace PredStructure

variable (P : PredStructure.{u})

/-! ## Strict ω-chains (Definition 5.1) -/

/-- A strict ω-chain in `(A, ≺)` is a function `s : ℕ → A` such that
    `s(n) ≺ s(n+1)` for all `n` (Definition 5.1). -/
structure StrictOmegaChain where
  seq : ℕ → P.carrier
  strict : ∀ n, P.prec (seq n) (seq (n + 1))

/-! ## Cofinal Refinement (Definition 5.2) -/

/-- A cofinal refinement from chain `s` to chain `t` is a strictly increasing
    function `φ : ℕ → ℕ` such that `s(n) ≃_Geom t(φ(n))` for all `n`
    (Definition 5.2). -/
def CofinalRefines (s t : P.StrictOmegaChain) : Prop :=
  ∃ (phi : ℕ → ℕ), StrictMono phi ∧ ∀ n, PredGeomEquiv P P (s.seq n) (t.seq (phi n))

/-! ## Cofinal Equivalence (Definition 5.3) -/

/-- Two chains are cofinally equivalent `s ~_cof t` iff
    `s ≼_cof t` and `t ≼_cof s` (Definition 5.3). -/
def CofinalEquiv (s t : P.StrictOmegaChain) : Prop :=
  P.CofinalRefines s t ∧ P.CofinalRefines t s

/-- Cofinal equivalence is reflexive. -/
theorem CofinalEquiv.rfl' (s : P.StrictOmegaChain) : P.CofinalEquiv s s :=
  ⟨⟨id, strictMono_id, fun n => PredGeomEquiv.refl P _⟩,
   ⟨id, strictMono_id, fun n => PredGeomEquiv.refl P _⟩⟩

/-- Cofinal equivalence is symmetric. -/
theorem CofinalEquiv.symm' {s t : P.StrictOmegaChain}
    (h : P.CofinalEquiv s t) : P.CofinalEquiv t s :=
  ⟨h.2, h.1⟩

/-- Cofinal refinement is transitive. -/
theorem CofinalRefines.trans' {s t u : P.StrictOmegaChain}
    (h₁ : P.CofinalRefines s t) (h₂ : P.CofinalRefines t u) :
    P.CofinalRefines s u := by
  obtain ⟨φ₁, hφ₁, hc₁⟩ := h₁
  obtain ⟨φ₂, hφ₂, hc₂⟩ := h₂
  exact ⟨φ₂ ∘ φ₁, hφ₂.comp hφ₁, fun n => PredGeomEquiv.trans (hc₁ n) (hc₂ (φ₁ n))⟩

/-- Cofinal equivalence is transitive. -/
theorem CofinalEquiv.trans' {s t u : P.StrictOmegaChain}
    (h₁ : P.CofinalEquiv s t) (h₂ : P.CofinalEquiv t u) :
    P.CofinalEquiv s u :=
  ⟨CofinalRefines.trans' P h₁.1 h₂.1, CofinalRefines.trans' P h₂.2 h₁.2⟩

/-- Cofinal equivalence is an equivalence relation on strict ω-chains. -/
theorem cofinalEquiv_equivalence : Equivalence P.CofinalEquiv where
  refl := CofinalEquiv.rfl' P
  symm := fun h => CofinalEquiv.symm' P h
  trans := fun h₁ h₂ => CofinalEquiv.trans' P h₁ h₂

end PredStructure
