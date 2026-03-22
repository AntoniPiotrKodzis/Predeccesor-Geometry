/-
# The Σ-Closure: General Signature Framework

Formalization of Sections 3–4 of the preprint:
- Shape apparatus and closure signatures (Definition 3.1, 3.2)
- Σ-algebras (Definition 4.6)
- The Σ-closure `Next_Σ(A)` (Definition 4.1, schema)
- Initiality of the Σ-closure (Theorem 4.7)
-/
import Mathlib
import RequestProject.Basic

universe u

/-! ## Closure Signatures (Definitions 3.1–3.2) -/

/-- A closure signature specifies admissible diagram shapes and cofinal equivalence
    (Definitions 3.1 and 3.2).

    For simplicity we use a single "presentation" type bundling shape codes and diagrams. -/
structure ClosureSignature (P : PredStructure.{u}) where
  /-- Type of presentations (pairs of shape code and diagram). -/
  Pres : Type u
  /-- Decoded index type for each presentation. -/
  IndexType : Pres → Type u
  /-- Index predecessor relation. -/
  indexPrec : ∀ p : Pres, IndexType p → IndexType p → Prop
  /-- The diagram labeling: for each presentation and index, an element of A. -/
  label : ∀ p : Pres, IndexType p → P.carrier
  /-- Labels are monotone with respect to index predecessor relation. -/
  labelMono : ∀ (p : Pres) (i j : IndexType p),
    indexPrec p i j → P.prec (label p i) (label p j)
  /-- Cofinal equivalence relation on presentations. -/
  cofEq : Pres → Pres → Prop
  cofEq_refl : ∀ p, cofEq p p
  cofEq_symm : ∀ p q, cofEq p q → cofEq q p
  cofEq_trans : ∀ p q r, cofEq p q → cofEq q r → cofEq p r

namespace ClosureSignature

variable {P : PredStructure.{u}} (sig : ClosureSignature P)

/-! ## Σ-Algebras (Definition 4.6) -/

/-- A Σ-algebra over `(A, ≺)` (Definition 4.6). -/
structure SigmaAlgebra where
  X : PredStructure.{u}
  f₀ : P.carrier → X.carrier
  f₀_mono : ∀ x y, P.prec x y → X.prec (f₀ x) (f₀ y)
  lub : sig.Pres → X.carrier
  lub_upper : ∀ (p : sig.Pres) (i : sig.IndexType p),
    X.prec (f₀ (sig.label p i)) (lub p)
  lub_cofinal : ∀ (p q : sig.Pres), sig.cofEq p q → lub p = lub q

/-! ## Points of the Σ-closure (Definition 4.1) -/

/-- Points of the Σ-closure `Next_Σ(A)`. -/
inductive NextSigmaPoint where
  | base : P.carrier → NextSigmaPoint
  | sup : sig.Pres → NextSigmaPoint

/-- The generated predecessor relation on `Next_Σ(A)` (Definition 4.1). -/
inductive NextSigmaPrec : sig.NextSigmaPoint → sig.NextSigmaPoint → Prop where
  | liftBase {x y : P.carrier} : P.prec x y →
      NextSigmaPrec (.base x) (.base y)
  | diagBelow {p : sig.Pres} (i : sig.IndexType p) :
      NextSigmaPrec (.base (sig.label p i)) (.sup p)
  | downClose {u : sig.NextSigmaPoint} {p : sig.Pres} {i : sig.IndexType p} :
      NextSigmaPrec u (.base (sig.label p i)) →
      NextSigmaPrec u (.sup p)

/-- The Σ-closure as a predecessor structure. -/
def NextSigma : PredStructure where
  carrier := sig.NextSigmaPoint
  prec := sig.NextSigmaPrec

/-! ## Initiality (Theorem 4.7) -/

/-- The recursor for `Next_Σ(A)`: given a Σ-algebra, define the unique map out
    (Theorem 4.7, existence). -/
def nextSigmaRecursor (alg : sig.SigmaAlgebra) : sig.NextSigmaPoint → alg.X.carrier
  | .base a => alg.f₀ a
  | .sup p => alg.lub p

/-- Uniqueness of the recursor (Theorem 4.7, uniqueness). -/
theorem nextSigmaRecursor_unique (alg : sig.SigmaAlgebra)
    (g : sig.NextSigmaPoint → alg.X.carrier)
    (hg_f₀ : ∀ a, g (.base a) = alg.f₀ a)
    (hg_lub : ∀ p, g (.sup p) = alg.lub p) :
    ∀ x, g x = sig.nextSigmaRecursor alg x := by
  intro x
  cases x with
  | base a => exact hg_f₀ a
  | sup p => exact hg_lub p

/-- The recursor commutes with `f₀`. -/
@[simp] theorem nextSigmaRecursor_base (alg : sig.SigmaAlgebra) (a : P.carrier) :
    sig.nextSigmaRecursor alg (.base a) = alg.f₀ a := rfl

/-- The recursor commutes with `lub`. -/
@[simp] theorem nextSigmaRecursor_sup (alg : sig.SigmaAlgebra) (p : sig.Pres) :
    sig.nextSigmaRecursor alg (.sup p) = alg.lub p := rfl

end ClosureSignature
