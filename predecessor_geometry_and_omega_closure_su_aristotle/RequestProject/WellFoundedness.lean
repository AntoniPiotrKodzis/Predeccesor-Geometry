/-
# Well-Foundedness Preservation

Formalization of Theorem 8.4 of the preprint:
- Well-foundedness of predecessor structures
- The ω-closure operator `Next_ω` preserves well-foundedness (Theorem 8.4, WF1)
- Extensional collapse preserves well-foundedness (Theorem 8.4, WF2)
-/
import Mathlib
import RequestProject.Basic
import RequestProject.OmegaChains
import RequestProject.BisimClosure

universe u

namespace PredStructure

variable (P : PredStructure.{u})

/-- A predecessor structure is well-founded if `prec` is well-founded. -/
def IsWellFounded : Prop :=
  WellFounded (fun x y => P.prec x y)

/-! ## The ω-closure carrier -/

/-- Points of the ω-closure `Next_ω(A)` (Definition 6.1).
    - `base a` for the base embedding `ι(a)`
    - `sup s` for the ω-supremum of a strict chain `s` -/
inductive NextOmegaPoint where
  | base : P.carrier → NextOmegaPoint
  | sup : P.StrictOmegaChain → NextOmegaPoint

/-- The generated predecessor relation `≺^ω` on `Next_ω(A)` (Definition 6.1). -/
inductive NextOmegaPrec : P.NextOmegaPoint → P.NextOmegaPoint → Prop where
  | liftBase {x y : P.carrier} : P.prec x y →
      NextOmegaPrec (.base x) (.base y)
  | chainBelow {s : P.StrictOmegaChain} (n : ℕ) :
      NextOmegaPrec (.base (s.seq n)) (.sup s)
  | downClose {u : P.NextOmegaPoint} {s : P.StrictOmegaChain} {n : ℕ} :
      NextOmegaPrec u (.base (s.seq n)) →
      NextOmegaPrec u (.sup s)

/-- The ω-closure as a predecessor structure. -/
def NextOmega : PredStructure where
  carrier := P.NextOmegaPoint
  prec := P.NextOmegaPrec

/-! ## Well-foundedness preservation (Theorem 8.4) -/

/-- Accessibility of base points in `Next_ω(A)` when `A` is well-founded. -/
theorem acc_nextOmega_base (hwf : P.IsWellFounded) (a : P.carrier) :
    Acc P.NextOmegaPrec (.base a) := by
  induction hwf.apply a with
  | intro a _ ih =>
    constructor
    intro u hu
    cases hu with
    | liftBase h => exact ih _ h

/-- Every predecessor of `sup(s)` is accessible when `A` is well-founded. -/
theorem acc_pred_of_sup (hwf : P.IsWellFounded) (s : P.StrictOmegaChain) :
    ∀ u, P.NextOmegaPrec u (.sup s) → Acc P.NextOmegaPrec u := by
  intro u hu
  cases hu with
  | chainBelow n => exact acc_nextOmega_base P hwf (s.seq n)
  | downClose h => exact (acc_nextOmega_base P hwf _).inv h

/-- `Next_ω(A)` is well-founded when `A` is well-founded
    (Theorem 8.4, WF1 specialized to the ω-signature). -/
theorem nextOmega_wellFounded (hwf : P.IsWellFounded) :
    P.NextOmega.IsWellFounded := by
  constructor
  intro x
  cases x with
  | base a => exact acc_nextOmega_base P hwf a
  | sup s =>
    constructor
    intro u hu
    exact acc_pred_of_sup P hwf s u hu

/-
PROBLEM
Well-foundedness is preserved by the extensional collapse (Theorem 8.4, WF2).
    Since the collapse is a quotient that only identifies elements (doesn't add new ones),
    and the predecessor relation on the quotient is induced, well-foundedness transfers.

PROVIDED SOLUTION
The well-foundedness of the extensional collapse follows because every element of the quotient ExtCollapse has an accessible representative in the original structure. Since the original structure P is well-founded (hwf), every element a is accessible. The quotient relation is defined by: x ≺_Ec y iff there exist representatives a, b with q(a)=x, q(b)=y, a ≺ b, x ≠ y. Since q is surjective (quotient map), for any ȳ, pick representative b, which is accessible in P. If x̄ ≺_Ec ȳ, then there exists a with a ≺ b, and a is accessible since b is (Acc is downward closed). Use well-founded induction on the original structure to show all quotient elements are accessible.
-/
theorem extCollapse_wellFounded (hwf : P.IsWellFounded)
    (hIrr : ∀ a, ¬P.prec a a)
    (hTrans : ∀ a b c, P.prec a b → P.prec b c → P.prec a c) :
    WellFounded (fun (x y : P.ExtCollapse) =>
      ∃ a b, P.extCollapseQuot a = x ∧ P.extCollapseQuot b = y ∧
             P.prec a b ∧ x ≠ y) := by
  -- Since the extensional collapse is a quotient of the original structure, we can use the well-foundedness of the original structure to conclude the well-foundedness of the quotient.
  have h_wf_quot : ∀ y : P.carrier, Acc P.prec y → ∀ x : P.carrier, P.prec x y → Acc (fun u v => ∃ a b : P.carrier, P.extCollapseQuot a = u ∧ P.extCollapseQuot b = v ∧ P.prec a b ∧ u ≠ v) (P.extCollapseQuot x) := by
    intros y hy x hxy
    generalize_proofs at *; (
    induction' hy with y hy ih generalizing x; simp_all +decide [ Acc ] ;
    refine' ⟨ _, fun z hz => _ ⟩;
    obtain ⟨ a, rfl, b, hb, hab, hne ⟩ := hz; specialize ih b; simp_all +decide [ PredStructure.extCollapse_eq_iff ] ;
    contrapose! ih; simp_all +decide [ PredGeomEquiv ] ;
    exact False.elim <| hne.elim <| by
      refine' { .. } <;> try tauto;)
  generalize_proofs at *; (
  have h_wf_quot : ∀ x : P.carrier, Acc P.prec x → Acc (fun u v => ∃ a b : P.carrier, P.extCollapseQuot a = u ∧ P.extCollapseQuot b = v ∧ P.prec a b ∧ u ≠ v) (P.extCollapseQuot x) := by
    intro x hx
    induction' hx with x ih
    generalize_proofs at *; (
    refine' ⟨ _, fun y hy => _ ⟩
    generalize_proofs at *; (
    obtain ⟨ a, b, rfl, hb, hab, hy ⟩ := hy; specialize h_wf_quot b ( hwf.apply b ) a hab; aesop;))
  generalize_proofs at *; (
  refine' ⟨ fun x => _ ⟩
  generalize_proofs at *; (
  obtain ⟨ a, rfl ⟩ := Quotient.exists_rep x; exact h_wf_quot a ( hwf.apply a ) ;)))

end PredStructure