/-
# Coherence of Quotient Paths

Formalization of Section 4.4 of the preprint:
- Set-truncated Σ-closure (Definition 4.5)
- UIP implies path coherence (Lemma 4.8)
- Canonical coherence laws for quotient paths (Proposition 4.9)

In Lean 4 with Prop-valued equality, these coherence results are automatic
since equality proofs in Prop are unique (proof irrelevance).
We formalize the structural content.
-/
import Mathlib
import RequestProject.Basic

universe u

/-! ## Lemma 4.8: In a set (0-type), identity proofs are unique -/

/-- In Lean 4, equality proofs are unique (proof irrelevance for Prop).
    This is the Lean analogue of Lemma 4.8 (UIP implies path coherence). -/
theorem eq_proof_unique {α : Sort u} (x y : α) (p q : x = y) : p = q :=
  Subsingleton.elim p q

/-! ## Proposition 4.9: Coherence laws for quotient paths -/

/-- Identity coherence: `rfl ▸ px = px` (Proposition 4.9, K1). -/
theorem transport_refl' {α : Type u} {P : α → Type*} (x : α) (px : P x) :
    @Eq.mpr (P x) (P x) rfl px = px := rfl

/-- Composition coherence: transport along composed paths equals composing
    transports (Proposition 4.9, K3). -/
theorem transport_trans' {α : Type u} {P : α → Type*} {x y z : α}
    (p : x = y) (q : y = z) (px : P x) :
    q ▸ (p ▸ px) = (p.trans q) ▸ px := by
  subst p; subst q; rfl

/-- Witness independence: any two parallel equalities give the same transport
    (Proposition 4.9, K4). -/
theorem transport_proof_irrel' {α : Type u} {P : α → Type*} {x y : α}
    (p q : x = y) (px : P x) :
    p ▸ px = q ▸ px := by
  cases Subsingleton.elim p q; rfl

/-! ## Theorem 4.10: Transport along cofinality paths is well-defined -/

/-- Transport is compatible with composition (Theorem 4.10, T1). -/
theorem transport_comp_compat' {α : Type u} {P : α → Type*} {x y z : α}
    (p : x = y) (q : y = z) (px : P x) :
    q ▸ p ▸ px = (p.trans q) ▸ px := by
  subst p; subst q; rfl

/-- Transport is independent of witness choice (Theorem 4.10, T2). -/
theorem transport_witness_indep' {α : Type u} {P : α → Type*} {x y : α}
    (p q : x = y) (px : P x) :
    p ▸ px = q ▸ px := by
  cases Subsingleton.elim p q; rfl

/-! ## The set-truncated closure: in Lean all types used as carriers
    are already "set-truncated" in the sense that equality is propositional. -/

/-- In Lean 4, the equality type on any type is a subsingleton (proof irrelevance).
    This is the formal content of Definition 4.5 (set-truncation) in the Lean setting.
    (Lean's equality lives in Prop, which is proof-irrelevant.) -/
example {α : Type u} (x y : α) : Subsingleton (x = y) :=
  ⟨fun p q => Subsingleton.elim p q⟩
