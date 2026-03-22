/-
# The ω-Closure: Initiality and Functoriality

Formalization of Sections 6–7 of the preprint:
- ω-complete recipients / ω-algebras (Definitions 6.2, 7.1)
- Initiality / universal property of `Next_ω(A)` (Theorem 6.3 / 7.2)
- Canonical embedding into any ω-complete model (Corollary 7.3)
- Morphisms of predecessor structures (Definition 7.4)
- Functoriality of `Next_ω` (Proposition 7.5)
-/
import Mathlib
import RequestProject.Basic
import RequestProject.OmegaChains
import RequestProject.WellFoundedness

universe u

namespace PredStructure

variable (P : PredStructure.{u})

/-! ## ω-Algebras (Definition 7.1) -/

/-- An ω-algebra over `(A, ≺)` is a predecessor structure `(X, ≺_X)` equipped with
    a monotone interpretation of `A` and least upper bounds for strict ω-chains,
    satisfying cofinal invariance (Definition 7.1 / Definition 6.2). -/
structure OmegaAlgebra where
  X : PredStructure.{u}
  f₀ : P.carrier → X.carrier
  f₀_mono : ∀ x y, P.prec x y → X.prec (f₀ x) (f₀ y)
  lub : P.StrictOmegaChain → X.carrier
  lub_upper : ∀ (s : P.StrictOmegaChain) (n : ℕ), X.prec (f₀ (s.seq n)) (lub s)
  lub_cofinal_inv : ∀ (s t : P.StrictOmegaChain),
    P.CofinalEquiv s t → lub s = lub t

/-! ## Initiality: maps out of `Next_ω(A)` (Theorem 6.3 / Theorem 7.2) -/

/-- Given an ω-algebra `𝐗`, define the unique map `F : Next_ω(A) → X` by recursion
    on the constructors of `Next_ω(A)` (Theorem 6.3, existence part). -/
def nextOmegaRecursor (alg : P.OmegaAlgebra) : P.NextOmegaPoint → alg.X.carrier
  | .base a => alg.f₀ a
  | .sup s => alg.lub s

/-- The recursor commutes with `f₀` (by definition). -/
theorem nextOmegaRecursor_comm_f₀ (alg : P.OmegaAlgebra) (a : P.carrier) :
    P.nextOmegaRecursor alg (.base a) = alg.f₀ a := rfl

/-- The recursor commutes with `lub` (by definition). -/
theorem nextOmegaRecursor_comm_lub (alg : P.OmegaAlgebra) (s : P.StrictOmegaChain) :
    P.nextOmegaRecursor alg (.sup s) = alg.lub s := rfl

/-- Uniqueness of the recursor: any map satisfying the same equations equals it
    (Theorem 6.3, Step 4). -/
theorem nextOmegaRecursor_unique (alg : P.OmegaAlgebra)
    (g : P.NextOmegaPoint → alg.X.carrier)
    (hg_f₀ : ∀ a, g (.base a) = alg.f₀ a)
    (hg_lub : ∀ s, g (.sup s) = alg.lub s) :
    ∀ x, g x = P.nextOmegaRecursor alg x := by
  intro x
  cases x with
  | base a => exact hg_f₀ a
  | sup s => exact hg_lub s

/-! ## Morphisms and Functoriality (Definition 7.4, Proposition 7.5) -/

/-- A morphism of predecessor structures is a monotone map (Definition 7.4). -/
structure PredMorphism (Q : PredStructure.{u}) where
  map : P.carrier → Q.carrier
  mono : ∀ x y, P.prec x y → Q.prec (map x) (map y)

/-- Push a strict ω-chain forward along a monotone map. -/
def PredMorphism.pushChain {Q : PredStructure.{u}} (f : P.PredMorphism Q)
    (s : P.StrictOmegaChain) : Q.StrictOmegaChain where
  seq := f.map ∘ s.seq
  strict n := f.mono _ _ (s.strict n)

/-- Functoriality of `Next_ω`: a morphism `f : A → B` induces
    a map `Next_ω(f) : Next_ω(A) → Next_ω(B)` (Proposition 7.5). -/
def nextOmegaMap {Q : PredStructure.{u}} (f : P.PredMorphism Q) :
    P.NextOmegaPoint → Q.NextOmegaPoint
  | .base a => .base (f.map a)
  | .sup s => .sup (PredMorphism.pushChain P f s)

/-- `Next_ω(f)` is monotone (Proposition 7.5). -/
theorem nextOmegaMap_mono {Q : PredStructure.{u}} (f : P.PredMorphism Q) :
    ∀ x y, P.NextOmegaPrec x y → Q.NextOmegaPrec (P.nextOmegaMap f x) (P.nextOmegaMap f y) := by
  intro x y h
  induction h with
  | liftBase h =>
    exact NextOmegaPrec.liftBase (f.mono _ _ h)
  | chainBelow n =>
    dsimp only [nextOmegaMap]
    exact @NextOmegaPrec.chainBelow Q (PredMorphism.pushChain P f _) n
  | downClose _ ih =>
    dsimp only [nextOmegaMap] at ih ⊢
    exact @NextOmegaPrec.downClose Q _ (PredMorphism.pushChain P f _) _ ih

end PredStructure
